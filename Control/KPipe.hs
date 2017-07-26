{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.KPipe where

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow
import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus (..), forever)
import Control.Monad.Fix
import Control.Monad.Trans.Class
import qualified Control.Exception as E
import Data.Void

newtype KPipe a y m t = KPipe {
    unKPipe
      :: forall r .
         (t -> m r)
      -> ((a -> KPipe a y m t) -> m r)
      -> (y -> KPipe a y m t -> m r)
      -> m r
  }

runKPipe :: forall m t . Applicative m =>  KPipe () Void m t -> m t
runKPipe (KPipe kpipe) =
  kpipe pure (\k -> runKPipe (k ())) absurd

keffect :: (forall r . (KPipe a y m t -> m r) -> m r) -> KPipe a y m t
keffect mkEffect = KPipe $ \done await yield ->
  mkEffect (\kpipe -> unKPipe kpipe done await yield)

effect :: Monad m => m t -> KPipe a y m t
effect it = KPipe $ \done _ _ -> it >>= done

kbracket :: IO r -> (r -> IO x) -> (r -> KPipe a y IO t) -> KPipe a y IO t
kbracket acquire release act = keffect $ \cc ->
  E.bracket acquire release $ \r -> cc (act r)

doneKPipe :: t -> KPipe a y m t
doneKPipe t = KPipe $ \done _ _ -> done t

awaitKPipe :: KPipe a y m a
awaitKPipe = KPipe $ \_ await _ -> await doneKPipe

yieldKPipe :: y -> KPipe a y m ()
yieldKPipe y = KPipe $ \_ _ yield -> yield y (doneKPipe ())

mapKPipe :: forall a y m s t . (s -> t) -> KPipe a y m s -> KPipe a y m t
mapKPipe f ~(KPipe kpipe) = KPipe $ \done await yield ->
  let done' = done . f
      await' = \k -> await (\a -> mapKPipe f (k a))
      yield' = \y next -> yield y (mapKPipe f next)
  in  kpipe done' await' yield'

apKPipe :: forall a y m s t . KPipe a y m (s -> t) -> KPipe a y m s -> KPipe a y m t
apKPipe (KPipe kpipeF) kpipeX = KPipe $ \done await yield ->
  let done' = \f -> unKPipe (mapKPipe f kpipeX) done await yield
      await' = \k -> await (\a -> apKPipe (k a) kpipeX)
      yield' = \y next -> yield y (apKPipe next kpipeX)
  in  kpipeF done' await' yield'

bindKPipe :: forall a y m s t . KPipe a y m s -> (s -> KPipe a y m t) -> KPipe a y m t
bindKPipe ~(KPipe kpipe) k = KPipe $ \done await yield ->
  let done' = \s -> unKPipe (k s) done await yield
      await' = \l -> await (\a -> bindKPipe (l a) k)
      yield' = \y next -> yield y (bindKPipe next k)
  in  kpipe done' await' yield'

instance Functor (KPipe a y m) where
  fmap = mapKPipe

instance Applicative (KPipe a y m) where
  pure = doneKPipe
  (<*>) = apKPipe

instance Monad (KPipe a y m) where
  return = pure
  (>>=) = bindKPipe

instance MonadTrans (KPipe a y) where
  lift = effect

seqKPipe
  :: forall a x y m t .
     KPipe a x m t
  -> KPipe x y m t
  -> KPipe a y m t
seqKPipe ~left@(KPipe pipeL) ~right@(KPipe pipeR) = KPipe $ \(done :: t -> m r) await yield ->
  let
      rAwait :: (x -> KPipe x y m t) -> m r
      rAwait continue = pipeL done (\k -> await (\a -> seqKPipe (k a) right)) (lYield continue)

      rYield :: y -> KPipe x y m t -> m r
      rYield y next = yield y (seqKPipe left next)

      -- Use of unKPipe is dubious, no?
      -- Maybe it's right...
      lYield :: (x -> KPipe x y m t) -> x -> KPipe a x m t -> m r
      lYield continue x next = unKPipe (seqKPipe next (continue x)) done await yield

  in  pipeR done rAwait rYield

-- | Yield 'Just' until the pipe is dead, at which point 'Nothing' is
-- yielded again and again.
exhaust :: KPipe a y m t -> KPipe a (Maybe y) m x
exhaust pipe = do
  _ <- pipe `seqKPipe` mkJust
  forever (yieldKPipe Nothing)
  where
  mkJust = do
    y <- awaitKPipe
    yieldKPipe (Just y)
    mkJust

emptyKPipe :: Alternative m => KPipe a y m t
emptyKPipe = KPipe $ \_ _ _ -> empty

altKPipe :: Alternative m => KPipe a y m t -> KPipe a y m t -> KPipe a y m t
altKPipe ~(KPipe pipeL) ~(KPipe pipeR) = KPipe $ \done await yield ->
  pipeL done await yield <|> pipeR done await yield

instance Alternative m => Alternative (KPipe a y m) where
  empty = emptyKPipe
  (<|>) = altKPipe

zeroKPipe :: MonadPlus m => KPipe a y m t
zeroKPipe = KPipe $ \_ _ _ -> mzero

plusKPipe :: MonadPlus m => KPipe a y m t -> KPipe a y m t -> KPipe a y m t
plusKPipe ~(KPipe pipeL) ~(KPipe pipeR) = KPipe $ \done await yield ->
  pipeL done await yield `mplus` pipeR done await yield

instance MonadPlus m => MonadPlus (KPipe a y m) where
  mzero = zeroKPipe
  mplus = plusKPipe

newtype Codensity f t = Codensity {
    unCodensity :: forall r . (t -> f r) -> f r
  }

fixKPipe :: forall m t . MonadFix m => (t -> KPipe () Void m t) -> KPipe () Void m t
fixKPipe f = KPipe $ \done _ _ ->
  mfix (\t -> let n = f t in runKPipe n) >>= done

instance MonadFix m => MonadFix (KPipe () Void m) where
  mfix = fixKPipe

hoistKPipe
  :: forall a y m n t .
     (forall x . m x -> n x)
  -> (forall x . n x -> m x)
  -> KPipe a y m t
  -> KPipe a y n t
hoistKPipe nat rnat (KPipe kpipe) = KPipe $ \done await yield ->
  let done' = rnat . done
      await' = \k -> rnat (await (\a -> hoistKPipe nat rnat (k a)))
      yield' = \y next -> rnat (yield y (hoistKPipe nat rnat next))
  in  nat $ kpipe done' await' yield'

-- | Use a Kleisli arrow as a KPipe by awaiting the input, running the
-- effect, and yielding the output.
--
-- This gives a way to bring more general arrows into KPipe by first
-- transforming them into Kleisli arrows over the relevant monad
--
--   forall a b . arrow a b -> Kleisli m a b
--
--
kleisliKPipe :: Monad m => Kleisli m a y -> KPipe a y m ()
kleisliKPipe kleisli = do
  a <- awaitKPipe
  y <- effect $ runKleisli kleisli a
  yieldKPipe y

arrowKPipe :: Monad m => (forall s t . f s t -> Kleisli m s t) -> f a y -> KPipe a y m ()
arrowKPipe nat = kleisliKPipe . nat

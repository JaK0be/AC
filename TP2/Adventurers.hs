{-# LANGUAGE FlexibleInstances #-}
module Adventurers where

import Data.List
import Data.Either
import Control.Monad

import DurationMonad

-- The list of adventurers
data Adventurer = P1 | P2 | P5 | P10 deriving (Show,Eq)
-- Adventurers + the lantern
type Objects = Either Adventurer ()

-- The time that each adventurer needs to cross the bridge
-- To implement 
getTimeAdv :: Adventurer -> Int
getTimeAdv P1 = 1
getTimeAdv P2 = 2
getTimeAdv P5 = 5
getTimeAdv P10 = 10

{-- The state of the game, i.e. the current position of each adventurer
+ the lantern. The function (const False) represents the initial state
of the game, with all adventurers and the lantern on the left side of
the bridge. Similarly, the function (const True) represents the end
state of the game, with all adventurers and the lantern on the right
side of the bridge.  --}
type State = Objects -> Bool

instance Show State where
  show s = (show . (fmap show)) [s (Left P1),
                                 s (Left P2),
                                 s (Left P5),
                                 s (Left P10),
                                 s (Right ())]

instance Eq State where
  (==) s1 s2 = and [s1 (Left P1) == s2 (Left P1),
                    s1 (Left P2) == s2 (Left P2),
                    s1 (Left P5) == s2 (Left P5),
                    s1 (Left P10) == s2 (Left P10),
                    s1 (Right ()) == s2 (Right ())]



-- The initial state of the game
gInit :: State
gInit = const False

gEx1 :: State
gEx1 (Left P1) = True
gEx1 _  = False

gFinal :: State
gFinal = const True

-- Changes the state of the game for a given object
changeState :: Objects -> State -> State
changeState a s = let v = s a in (\x -> if x == a then not v else s x)

-- Changes the state of the game of a list of objects
mChangeState :: [Objects] -> State -> State
mChangeState os s = foldr changeState s os

{-- For a given state of the game, the function presents all the
possible moves that the adventurers can make.  --}
-- To implement
allValidPlays :: State -> ListDur State
allValidPlays s = let lantern = s $ Right ()
                      adventurers = filter (\x -> s x == lantern) [Left P1, Left P2, Left P5, Left P10]
                      adventurerMoves = map (\l -> (Right ()) : l) (subsets 1 adventurers ++ subsets 2 adventurers)
                  in LD $ map (\moves -> Duration (maximum (map getTimeAdv (lefts moves)), mChangeState moves s)) adventurerMoves

subsets 0 _ = [[]]
subsets _ [] = []
subsets n (x : xs) = map (x :) (subsets (n - 1) xs) ++ subsets n xs



{-- For a given number n and initial state, the function calculates
all possible n-sequences of moves that the adventures can make --}
-- To implement
exec :: Int -> State -> ListDur State
exec 0 s = return s
exec n s = do s' <- allValidPlays s
              s'' <- exec (n - 1) s'
              return s''

{-- Calculate all possible states from the beginning up to n --}
execUpTo :: Int -> State -> ListDur State
execUpTo n s = manyChoice $ map (\i -> exec i s) [0..n]

{-- Is it possible for all adventurers to be on the other side
in <=17 min and not exceeding 5 moves ? --}
-- To implement
leq17 :: Bool
leq17 = any reachedAndLeq17 (remLD $ execUpTo 5 gInit)
            where reachedAndLeq17 (Duration (d, s)) = d <= 17 && s == gFinal

{-- Is it possible for all adventurers to be on the other side
in < 17 min ? --}
-- To implement
l17 :: Bool
l17 = any reachedAndL17 (remLD $ execUpTo 5 gInit)
          where reachedAndL17 (Duration (d, s)) = d < 17 && s == gFinal


--------------------------------------------------------------------------
{-- Implementation of the monad used for the problem of the adventurers.
Recall the Knight's quest --}

data ListDur a = LD [Duration a] deriving Show

remLD :: ListDur a -> [Duration a]
remLD (LD x) = x

-- To implement
instance Functor ListDur where
    fmap f =
        let f' = \(d, x) -> (d, f x) in
            LD . map (Duration . f' . remDur) . remLD


-- To implement
instance Applicative ListDur where
   pure x = LD [Duration (0, x)]
   l1 <*> l2 = LD $ do x <- remLD l1
                       y <- remLD l2
                       g (remDur x, remDur y) where
                           g ((d1, f), (d2, x)) = return $ Duration (d1 + d2, f x)

-- To implement
instance Monad ListDur where
   return = pure
   l >>= k = LD $ do a <- remLD l
                     g (remDur a) where
                     g (d, x) = let u = (remLD (k x)) in map ((\(d',x) -> Duration (d + d', x)) . remDur) u

manyChoice :: [ListDur a] -> ListDur a
manyChoice = LD . concat . (map remLD)
--------------------------------------------------------------------------

{-- LogListDur monad --}

allValidPlays' :: State -> ListDur [State]
allValidPlays' s = let lantern = s $ Right ()
                       adventurers = filter (\x -> s x == lantern) [Left P1, Left P2, Left P5, Left P10]
                       adventurerMoves = map (\l -> (Right ()) : l) (subsets 1 adventurers ++ subsets 2 adventurers)
                   in LD $ map (\moves -> Duration (maximum (map getTimeAdv (lefts moves)), [mChangeState moves s])) adventurerMoves

{-- For a given number n and initial trace, the function calculates
all possible n-sequences of traces that the adventures can make --}
-- To implement
exec' :: Int -> [State] -> ListDur [State]
exec' 0 s = return s
exec' n s = do s' <- allValidPlays' (last s)
               s'' <- exec' (n - 1) (s ++ s')
               return s''

{-- Calculate all possible traces from the beginning up to n --}
execUpTo' :: Int -> [State] -> ListDur [State]
execUpTo' n s = manyChoice $ map (\i -> exec' i s) [0..n]

{-- Is it possible for all adventurers to be on the other side
in <=17 min and not exceeding 5 moves ? --}
-- To implement
leq17' :: [(ListDur [State])]
leq17' = [LD [trace] | trace <- remLD $ execUpTo' 5 [gInit], reachedAndLeq17 trace]
          where reachedAndLeq17 (Duration (d, s)) = d <= 17 && last s == gFinal

{-- Is it possible for all adventurers to be on the other side
in < 17 min ? --}
-- To implement
l17' :: [(ListDur [State])]
l17' = [LD [trace] | trace <- remLD $ execUpTo' 5 [gInit], reachedAndL17 trace]
          where reachedAndL17 (Duration (d, s)) = d < 17 && last s == gFinal

{-- Check if the lantern changes sides each trasition, and if the only adventurers who also change sides go in the same direction as the lantern. --}
checkLanternSafety :: Int -> Bool
checkLanternSafety n =
    let traces = remLD $ exec' n [gInit]
    in all (checkTrace . getValue) traces
       where checkTrace (h1:h2:t) = (h1 (Right ())) /= (h2 (Right ())) && (checkCrossing h1 h2) && checkTrace (h2:t)
             checkTrace _ = True
             checkCrossing t1 t2 = all (\a -> t1 a == t2 a || t2 a == t2 (Right ())) [Left P1, Left P2, Left P5, Left P10]

count :: (a -> Bool) -> [a] -> Int
count _ [] = 0
count p (x:xs) | p x       = 1 + count p xs
               | otherwise = count p xs

{-- Check if a maximum of 2 adventurers change side each transition --}
checkAdventurersSafety :: Int -> Bool
checkAdventurersSafety n =
    let traces = remLD $ exec' n [gInit]
    in all (checkTrace . getValue) traces
        where checkTrace (h1:h2:t) = (checkCrossingLeq2 h1 h2) && checkTrace (h2:t)
              checkTrace _ = True
              checkCrossingLeq2 t1 t2 = (count (\a -> t1 a /= t2 a) [Left P1, Left P2, Left P5, Left P10]) <= 2

{-- Check if generated traces have the correct duration --}
checkTraceDuration :: Int -> Bool
checkTraceDuration n =
    let traces = remLD $ execUpTo' n [gInit]
    in all (\t -> (calculateDuration . getValue) t == (getDuration t)) traces
        where calculateDuration (h1:h2:t) = (calculateTransitionDuration h1 h2) + calculateDuration (h2:t)
              calculateDuration _ = 0
              calculateTransitionDuration t1 t2 =
                  let adventurers = filter (\x -> t1 x /= t2 x) [Left P1, Left P2, Left P5, Left P10]
                  in maximum $ map getTimeAdv $ lefts adventurers


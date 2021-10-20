import CNF
import CNF.DIMACS

import qualified Solver.Naive as Naive
import qualified Solver.Backtracking as Backtracking
import qualified Tests.Tester as Tester

import Control.Monad
import System.Environment
import System.Exit

main :: IO ()
main = do
  name <- getProgName
  args <- getArgs
  unless (length args == 1) $ do
    putStrLn ("Usage: " ++ name ++ " <cnf file>")
    exitFailure
  f <- readCNFfromDIMACS (args !! 0)
  case Backtracking.solution f of
    Nothing  -> putStrLn "UNSAT"
    Just rho -> putStrLn ("SAT\n" ++ dimacsSubst rho ++ "\nValide : " ++ show (Tester.test rho f))

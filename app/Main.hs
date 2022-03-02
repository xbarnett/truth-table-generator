module Main where
import qualified Data.Char as C
import qualified Data.Functor.Identity as F
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified System.IO as I
import qualified Text.Parsec as P
import qualified Text.Parsec.Expr as P
import qualified Text.Parsec.String as P

data Expr = Var Char |
  Not Expr |
  And Expr Expr |
  Or Expr Expr |
  Xor Expr Expr |
  Cond Expr Expr |
  Bicond Expr Expr
  deriving (Show)

parse_var :: P.Parser (Expr, [String])
parse_var = do
  result <- P.lower
  return (Var result, [[result]])

paren_type :: String -> String -> P.Parser (Expr, [String])
  -> P.Parser (Expr, [String])
paren_type p0 p1 parser = do
  P.string p0
  (e, s0) <- parser
  P.string p1
  let s1 = (p0 ++ head s0) : tail s0
  let s2 = init s1 ++ [last s1 ++ p1]
  return (e, s2)

paren_strings :: [(String, String)]
paren_strings = [("(", ")"), ("[", "]"), ("{", "}")]

parens :: P.Parser (Expr, [String]) -> P.Parser (Expr, [String])
parens parser = P.choice (map (\(p0, p1) -> paren_type p0 p1 parser)
  paren_strings)

parse_term :: P.Parser (Expr, [String])
parse_term = do
  P.spaces
  result <- parens parse_expr P.<|> parse_var
  P.spaces
  return result

data Operator = Prefix String [String] (Expr -> Expr) |
  Infix String [String] (Expr -> Expr -> Expr) P.Assoc

operators :: [[Operator]]
operators = [
  [Prefix "\\sim" ["~", "-", "not"] Not],
  [Infix "\\land" ["&", "&&", "^", "*", "and"] And P.AssocLeft,
   Infix "\\lor" ["|", "||", "+", "v", "or"] Or P.AssocLeft,
   Infix "\\oplus" ["x", "xor"] Xor P.AssocLeft],
  [Infix "\\to" [">", "->", "to", "implies"] Cond P.AssocLeft,
   Infix "\\leftrightarrow" ["<>", "<->", "iff"] Bicond P.AssocLeft]]

op_chars :: [Char]
op_chars = do
  ops <- operators
  op <- ops
  let ss = case op of
             (Prefix _ ss _) -> ss
             (Infix _ ss _ _) -> ss
  s <- ss
  c <- s
  return c

convert_op :: Operator -> [P.Operator String () F.Identity (Expr, [String])]
convert_op (Prefix lname names fun) = map (\name -> P.Prefix (do
  P.try (P.string name >> P.notFollowedBy (P.oneOf op_chars))
  return (\(e0, s0) -> (fun e0, lname : s0)))) names
convert_op (Infix lname names fun assoc) = map (\name -> P.Infix (do
  P.try (P.string name >> P.notFollowedBy (P.oneOf op_chars))
  return (\(e0, s0) (e1, s1) -> (fun e0 e1, s0 ++ [lname] ++ s1)))
    assoc) names

parse_expr :: P.Parser (Expr, [String])
parse_expr = P.buildExpressionParser (map (concat . (map convert_op)) operators)
  parse_term

modify_header_string :: String -> String
modify_header_string s = (if (null s0) then "" else ("\\llap{" ++ s0 ++ "}"))
  ++ s1 ++ (if (null s2) then "" else ("\\rlap{" ++ s2 ++ "}"))
  where
    pchars :: [Char]
    pchars = concat (map (uncurry (++)) paren_strings)

    s0 :: String
    s0 = takeWhile (\c -> elem c pchars) s

    s2 :: String
    s2 = reverse (takeWhile (\c -> elem c pchars) (reverse s))

    s1 :: String
    s1 = [c | (i, c) <- zip [0..] s, i >= length s0, i < length s - length s2]

parse_input :: P.Parser (Expr, [String])
parse_input = do
  (e, ss) <- parse_expr
  P.eof
  return (e, map modify_header_string ss)

get_vars :: Expr -> [Char]
get_vars (Var c) = [c]
get_vars (Not a) = get_vars a
get_vars (And a b) = get_vars a ++ get_vars b
get_vars (Or a b) = get_vars a ++ get_vars b
get_vars (Xor a b) = get_vars a ++ get_vars b
get_vars (Cond a b) = get_vars a ++ get_vars b
get_vars (Bicond a b) = get_vars a ++ get_vars b

get_sorted_vars :: Expr -> [Char]
get_sorted_vars = S.toList . S.fromList . get_vars

powerset :: [Char] -> [M.Map Char Bool]
powerset [] = [M.empty]
powerset (x:xs) = map (M.insert x True) p ++ map (M.insert x False) p
  where
    p :: [M.Map Char Bool]
    p = powerset xs

cond :: Bool -> Bool -> Bool
cond True b = b
cond False _ = True

evaluate :: M.Map Char Bool -> Expr -> ([Bool], Int)
evaluate m (Var s) = ([m M.! s], 0)
evaluate m (Not a) = (val : xs, 0)
  where
    xs :: [Bool]
    i :: Int
    (xs, i) = evaluate m a

    val :: Bool
    val = not (xs !! i)
evaluate m (And a b) = (xs ++ [val] ++ ys, length xs)
  where
    xs :: [Bool]
    i :: Int
    (xs, i) = evaluate m a

    ys :: [Bool]
    j :: Int
    (ys, j) = evaluate m b

    val :: Bool
    val = (xs !! i) && (ys !! j)
evaluate m (Or a b) = (xs ++ [val] ++ ys, length xs)
  where
    xs :: [Bool]
    i :: Int
    (xs, i) = evaluate m a

    ys :: [Bool]
    j :: Int
    (ys, j) = evaluate m b

    val :: Bool
    val = (xs !! i) || (ys !! j)
evaluate m (Xor a b) = (xs ++ [val] ++ ys, length xs)
  where
    xs :: [Bool]
    i :: Int
    (xs, i) = evaluate m a

    ys :: [Bool]
    j :: Int
    (ys, j) = evaluate m b

    val :: Bool
    val = (xs !! i) /= (ys !! j)
evaluate m (Cond a b) = (xs ++ [val] ++ ys, length xs)
  where
    xs :: [Bool]
    i :: Int
    (xs, i) = evaluate m a

    ys :: [Bool]
    j :: Int
    (ys, j) = evaluate m b

    val :: Bool
    val = cond (xs !! i) (ys !! j)
evaluate m (Bicond a b) = (xs ++ [val] ++ ys, length xs)
  where
    xs :: [Bool]
    i :: Int
    (xs, i) = evaluate m a

    ys :: [Bool]
    j :: Int
    (ys, j) = evaluate m b

    val :: Bool
    val = (xs !! i) == (ys !! j)

truth_table :: Expr -> (Int, [([Bool], [Bool])])
truth_table e = (snd (evaluate (head p) e),
                 map (\m -> ((M.elems m), fst (evaluate m e))) p)
  where
    p :: [M.Map Char Bool]
    p = powerset (get_sorted_vars e)

bool_to_str :: Bool -> String
bool_to_str True = "T"
bool_to_str False = "F"

get_latex :: Expr -> [String] -> String
get_latex e ss = unlines ([
  "\\[",
  "\\begin{tabular}{" ++ (concat (replicate first_width "|c")) ++ "||" ++
    (replicate i 'c') ++ "g" ++ (replicate (length ss - i - 1) 'c') ++ "|}",
  "  \\hline",
  "  \\rowcolor{white}",
  "  " ++ L.intercalate " & " (map (\s -> "$" ++ s ++ "$") (vars ++ ss))
    ++ " \\\\",
  "  \\hline"] ++ map (\bs -> "  " ++ L.intercalate " & " (map bool_to_str bs)
                        ++ " \\\\") (map (uncurry (++)) rows) ++ [
  "  \\hline",
  "\\end{tabular}",
  "\\]"])
  where
    i :: Int
    rows :: [([Bool], [Bool])]
    (i, rows) = truth_table e

    first_width :: Int
    first_width = length (fst (head rows))

    vars :: [String]
    vars = map (\c -> [c]) (get_sorted_vars e)

loop :: Int -> IO ()
loop i = do
  eof <- I.isEOF
  if eof then return () else do
    s <- getLine
    case P.parse parse_input "" s of
      (Left e) -> error ("failure on line " ++ show i ++ ": " ++ show e)
      (Right (expr, expr_strings)) -> do
        putStrLn (get_latex expr expr_strings)
        loop (i + 1)

main :: IO ()
main = loop 1

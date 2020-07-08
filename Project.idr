{-
Load the file first using ":l Project.idr"
Type "main" and run it to see results.
-}
import Data.HVect
import Data.Vect
import Data.Vect.Quantifiers

-- Defining matrix as a vector of vectors
Matrix :  Nat -> Nat -> Type -> Type
Matrix row col a = Vect row (Vect col a)

---Helper methods---
--An empty matrix
empty_matrix : Vect row (Vect 0 a)
empty_matrix {row = Z} = []
empty_matrix {row = (S k)} = [] :: empty_matrix

multiplication_helper2 : Num a => Vect m a -> Vect m a -> a
multiplication_helper2 [] [] = 0
multiplication_helper2 (r :: rs) (c :: cs) = r * c + multiplication_helper2 rs cs

multiplication_helper1 : Num a => Vect col a -> Matrix row col a -> Vect row a
multiplication_helper1 {row = Z} rs [] = replicate Z 0
multiplication_helper1 {row = (S k)} rs (c :: cs) = (multiplication_helper2 rs c) :: multiplication_helper1 rs cs

transposition_helper : (r : Vect col a) -> (r_t : Vect col (Vect row a)) -> Vect col (Vect (S row) a)
transposition_helper [] [] = []
transposition_helper (x :: xs) (y :: ys) = (x :: y) :: transposition_helper xs ys

--Addition of two matrices
addition : Num a => Matrix row col a -> Matrix row col a -> Matrix row col a
addition []        []        = []
addition (r :: rs) (c :: cs) = zipWith (+) r c :: addition rs cs

--Subtraction of two matrices
subtraction : Neg a => Matrix r c a -> Matrix r c a -> Matrix r c a
subtraction []        []        = Nil
subtraction (r :: rs) (c :: cs) =  zipWith (-) r c :: subtraction rs cs

--Transposition of a Matrix
transposition: Matrix row col a -> Matrix col row a
transposition [] = empty_matrix
transposition (r :: rs) = let r_t = transposition rs in transposition_helper r r_t

--Multiplication of two matrices
multiplication : Num a => Matrix row1 com a -> Matrix com col2 a -> Matrix row1 col2 a
multiplication [] [] = []
multiplication [] (r :: rs) = []
multiplication (r :: rs) mat = let transposed = transposition mat in (multiplication_helper1 r transposed) :: multiplication rs mat

--Scaling
scale : (Num a)=> a -> Matrix row col a  -> Matrix row col a
scale _ []  = Nil
scale scale_value (r::rs)  = (map (\c => c*scale_value) r) :: scale scale_value rs

--Testing
mat1 : Matrix 2 2 Double
mat1 = ( -1 :: 2 ::  Nil) :: ( 4 :: 5 :: Nil) :: Nil

mat2 : Matrix 2 2 Double
mat2 = ( -7 :: 8 :: Nil) :: ( 9 :: 10 :: Nil) :: Nil

main : String
main = "Matrix 1: " ++ show(mat1) ++
  "\n  Matrix 2: " ++ show(mat2) ++
  "\n  Addition: " ++ (show (addition mat1 mat2)) ++
  "\n  Subtraction: " ++ (show (subtraction mat1 mat2)) ++
  "\n  Scaling of Matrix 1 by 2: " ++ (show (scale 2 mat1)) ++
  "\n  Multiplication: " ++ (show (multiplication mat1 mat2)) ++
  "\n  Transposition of Matrix 1: " ++ (show (transposition mat1))

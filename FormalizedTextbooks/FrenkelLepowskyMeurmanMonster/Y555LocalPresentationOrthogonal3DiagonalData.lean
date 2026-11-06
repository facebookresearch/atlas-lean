/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact independent diagonal coordinates of the nonsingular finite Cartan form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Data

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact diagonal weights of the independent finite Cartan form. -/
def y322Orthogonal3DiagonalWeight : Fin 7 → ZMod 3 :=
  ![2, 2, 1, 2, 2, 1, 2]

/-- An actual orthogonal coordinate basis of the independent finite Cartan form. -/
def y322Orthogonal3DiagonalBasisMatrix : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![
    ![1, 0, 2, 1, 0, 2, 0],
    ![0, 0, 1, 2, 0, 0, 0],
    ![0, 1, 2, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 2, 0],
    ![0, 0, 0, 0, 0, 1, 2],
    ![0, 0, 0, 0, 1, 2, 1],
    ![0, 0, 0, 0, 0, 0, 1]]

/-- The exact inverse coordinate basis matrix of the finite form. -/
def y322Orthogonal3DiagonalBasisInverseMatrix : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![
    ![1, 1, 0, 0, 1, 0, 1],
    ![0, 1, 1, 1, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 1],
    ![0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1]]

/-- The independent finite diagonal Gram matrix in these exact coordinates. -/
def y322Orthogonal3DiagonalGram : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  Matrix.diagonal y322Orthogonal3DiagonalWeight

set_option maxRecDepth 100000 in
-- The two small finite inverse matrix products are checked in the kernel.
/-- The exact diagonal coordinate basis matrices are mutual inverses. -/
theorem y322Orthogonal3DiagonalBasis_inverse :
    y322Orthogonal3DiagonalBasisMatrix * y322Orthogonal3DiagonalBasisInverseMatrix = 1 ∧
      y322Orthogonal3DiagonalBasisInverseMatrix * y322Orthogonal3DiagonalBasisMatrix = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
-- The exact finite congruence is checked on the literal independent Cartan matrix.
/-- The coordinate basis transports the actual original form to its exact diagonal Gram matrix. -/
theorem y322Orthogonal3DiagonalBasis_gram :
    y322Orthogonal3DiagonalBasisMatrix.transpose * y322Orthogonal3Gram *
        y322Orthogonal3DiagonalBasisMatrix = y322Orthogonal3DiagonalGram := by
  decide +kernel

/-- Every diagonal coordinate coefficient of the independent finite form is nonzero. -/
theorem y322Orthogonal3DiagonalWeight_ne_zero (i : Fin 7) :
    y322Orthogonal3DiagonalWeight i ≠ 0 := by
  fin_cases i <;> decide +kernel

/-- The exact diagonal basis as an actual invertible matrix. -/
def y322Orthogonal3DiagonalBasis : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3) where
  val := y322Orthogonal3DiagonalBasisMatrix
  inv := y322Orthogonal3DiagonalBasisInverseMatrix
  val_inv := y322Orthogonal3DiagonalBasis_inverse.1
  inv_val := y322Orthogonal3DiagonalBasis_inverse.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

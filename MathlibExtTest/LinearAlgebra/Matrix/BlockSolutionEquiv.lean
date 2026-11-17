/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv

@[expose] public section

open _root_.Matrix MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv

namespace MathlibExtTest.LinearAlgebra.Matrix.BlockSolutionEquiv

/-- A scalar (one-by-one block) system with a nonzero interior
right-hand side: `u = 1 * 1 + 2 * 2 = 5` and `v = 3 * 1 + 4 * 2 = 11`
both hold by computation. -/
example : (!![1] : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ![1] + !![2] *ᵥ ![2] = ![5]
    ∧ (!![3] : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ![1] + !![4] *ᵥ ![2] = ![11] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct]

/-- The reconstruction formula in the scalar case recovers `y = 2`
exactly, with the nonzero interior right-hand side `v = 11` surviving:
`(1/4) * (11 - 3) = 2`. -/
example : ![2] = (!![4] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ (![11] - !![3] *ᵥ ![1]) := by
  ext i
  fin_cases i
  norm_num [Matrix.mulVec, dotProduct, Matrix.inv_def, Matrix.adjugate_fin_one]

/-- With a nonsymmetric invertible interior block `D = !![2, 1; 0, 1]`,
elimination of a known solution returns the same interior unknown, for
arbitrary `x, y` satisfying the displayed system. -/
example : ∀ x y : Fin 2 → ℝ,
    (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x
        + !![1, 1; 0, 1] *ᵥ y = ![3, 4] →
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x
          + !![2, 1; 0, 1] *ᵥ y = ![5, 6] →
        y = (!![2, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
          *ᵥ (![5, 6] - !![0, 1; 1, 0] *ᵥ x) := by
  intro x y h1 h2
  letI : Invertible (!![2, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) :=
    Matrix.invertibleOfIsUnitDet _ (by norm_num)
  exact (elim_forward h1 h2).2

/-- The Schur complement of the scalar system, through the public
definition: `1 - 2 * (1/4) * 3 = -1/2`. -/
example : True := by
  letI : Invertible (!![4] : Matrix (Fin 1) (Fin 1) ℝ) :=
    Matrix.invertibleOfIsUnitDet _ (by norm_num [Matrix.det_fin_one])
  have h : schur (!![1] : Matrix (Fin 1) (Fin 1) ℝ) !![2] !![3] !![4]
      = !![-1 / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [schur, Matrix.inv_def, Matrix.adjugate_fin_one,
        Matrix.mul_apply, Finset.sum]
  trivial

end MathlibExtTest.LinearAlgebra.Matrix.BlockSolutionEquiv

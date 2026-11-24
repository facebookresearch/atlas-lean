/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GoldenThompson

/-!
# Tests for the Golden–Thompson file
-/

open scoped ComplexOrder

namespace MathlibExtTest.LinearAlgebra.Matrix.GoldenThompson

open MathlibExt.LinearAlgebra.Matrix.GoldenThompson

/-- A matrix commutes with its own multiples, so the commuting case applies. -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    (NormedSpace.exp (A + c • A)).trace = (NormedSpace.exp A * NormedSpace.exp (c • A)).trace :=
  trace_exp_add_of_commute ((Commute.refl A).smul_right c)

/-- Diagonal matrices commute. -/
example (d e : Fin 3 → ℂ) :
    (NormedSpace.exp (Matrix.diagonal d + Matrix.diagonal e)).trace ≤
      (NormedSpace.exp (Matrix.diagonal d) * NormedSpace.exp (Matrix.diagonal e)).trace :=
  golden_thompson_of_commute (Matrix.commute_diagonal d e)

/-- Positivity of the right side, for any pair of Hermitian matrices, here two noncommuting
Pauli matrices `σ_z` and `σ_x`. -/
example : 0 ≤ (NormedSpace.exp (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) *
    NormedSpace.exp (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)).trace := by
  refine trace_exp_mul_exp_nonneg ?_ ?_ <;>
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

end MathlibExtTest.LinearAlgebra.Matrix.GoldenThompson

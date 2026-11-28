/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.AitkenBlockIdentity
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Aitken's block identity

With two selected coordinates and one response coordinate, the independent computations check
that both formulas give the cross block $(5,-2)^{\mathsf T}$ and the response variance $16$.
The selected covariance and the original inverse are nondiagonal and do not commute.
-/

open Matrix

private def Sxx : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]
private def Sxy : Matrix (Fin 2) (Fin 1) ℝ := !![3; 1]
private def Syy : Matrix (Fin 1) (Fin 1) ℝ := !![9]
private def V : Matrix (Fin 2) (Fin 2) ℝ := !![3, 1; 1, 4]

private theorem Sxx_inv : Sxx⁻¹ = !![1, -1; -1, 2] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Sxx, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

-- Compute both sides of each equality without applying the theorem under test.
example :
    V * (Sxyᵀ * Sxx⁻¹)ᵀ = !![5; -2] ∧
    V * Sxx⁻¹ * Sxy = !![5; -2] ∧
    Sxyᵀ * Sxx⁻¹ * V * (Sxyᵀ * Sxx⁻¹)ᵀ + (Syy - Sxyᵀ * Sxx⁻¹ * Sxy) = !![16] ∧
    Syy - Sxyᵀ * (Sxx⁻¹ - Sxx⁻¹ * V * Sxx⁻¹) * Sxy = !![16] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Sxx_inv, Sxy, Syy, V, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one]

-- Apply both conclusions through the public API at the same rectangular blocks.
example :
    V * (Sxyᵀ * Sxx⁻¹)ᵀ = V * Sxx⁻¹ * Sxy ∧
    Sxyᵀ * Sxx⁻¹ * V * (Sxyᵀ * Sxx⁻¹)ᵀ + (Syy - Sxyᵀ * Sxx⁻¹ * Sxy) =
      Syy - Sxyᵀ * (Sxx⁻¹ - Sxx⁻¹ * V * Sxx⁻¹) * Sxy := by
  apply WantedExt.Biology.StatisticalGenetics.PearsonAitkenLawleySelectionWanted.aitken_block_identity
  · apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · norm_num [Sxx, Matrix.det_fin_two]

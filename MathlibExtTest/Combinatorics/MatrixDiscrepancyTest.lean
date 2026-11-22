/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MatrixDiscrepancy

open scoped BigOperators ENNReal
open MatrixDiscrepancy

namespace MathlibExtTest.MatrixDiscrepancy

example : ColumnAdmissible (fun _ _ : Fin 1 => (1 : ℝ)) :=
  columnAdmissible_unit

example : discrepancy (fun _ _ : Fin 1 => (1 : ℝ)) = 1 :=
  discrepancy_unit

example : (1 : ENNReal) ≤ komlosConstant := one_le_komlosConstant

example : ∃ x : Fin 1 → Fin 2,
    discrepancy (fun _ _ : Fin 1 => (1 : ℝ)) =
      ENNReal.ofReal ‖Matrix.mulVec (fun _ _ : Fin 1 => (1 : ℝ))
        (fun j => signValue (x j))‖ :=
  discrepancy_attained _

example : ∀ n : ℕ, dimensionConstant n ≤ n := dimensionConstant_le_dimension

example : dimensionConstant 1 = 1 := dimensionConstant_one

private noncomputable def cancellationMatrix : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1 / 2

example : ColumnAdmissible cancellationMatrix := by
  intro j
  norm_num [cancellationMatrix, Fin.sum_univ_two]

example : discrepancy cancellationMatrix = 0 := by
  apply le_antisymm ?_ bot_le
  have hz : cancellationMatrix.mulVec (fun j => signValue j) = 0 := by
    funext i
    norm_num [cancellationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, signValue]
  simpa [hz] using discrepancy_le_signing cancellationMatrix id

example : ‖cancellationMatrix.mulVec (fun _ => signValue 1)‖ = 1 := by
  have hv : cancellationMatrix.mulVec (fun _ => signValue 1) =
      fun _ : Fin 2 => (1 : ℝ) := by
    funext i
    norm_num [cancellationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, signValue]
  rw [hv]
  simp

example : dimensionConstant 0 = 0 := dimensionConstant_zero

example : discrepancy (0 : Matrix (Fin 2) (Fin 0) ℝ) = 0 := discrepancy_zero 2 0

example : ¬ColumnAdmissible (fun _ _ : Fin 2 => (1 : ℝ)) := by
  simp [ColumnAdmissible]

example : ColumnAdmissible cancellationMatrix ↔
    ∀ j, ‖(WithLp.toLp 2 (fun i => cancellationMatrix i j) : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 :=
  columnAdmissible_iff_euclidean _

example : komlosConstant < ⊤ ↔ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → dimensionConstant n ≤ ENNReal.ofReal c :=
  komlosConstant_lt_top_iff_eventual

#eval "C24 actual [1] admission, finite discrepancy and global lower proof elaborated"
#eval "C24 nonzero two-dimensional cancellation and zero-dimension proofs elaborated"

end MathlibExtTest.MatrixDiscrepancy

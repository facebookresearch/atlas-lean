/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.NikolovVectorColoring

open MatrixDiscrepancy KomlosDiscrepancyWanted

-- With two identical unit columns, orthogonal colors would give a row of norm √2.
example : ∃ u : Fin 2 → EuclideanSpace ℝ (Fin 2),
    (∀ j, ‖u j‖ = 1) ∧ ‖u 0 + u 1‖ ≤ 1 := by
  let A : Matrix (Fin 1) (Fin 2) ℝ := fun _ _ => 1
  have hA : ColumnAdmissible A := by simp [ColumnAdmissible, A]
  obtain ⟨u, hu, hrow⟩ := nikolov2013VectorColoringBound_holds 1 2 (by decide) A hA
  exact ⟨u, hu, by simpa [A, Fin.sum_univ_two] using hrow 0⟩

-- An empty row set still requires a unit color for every column.
example : ∃ u : Fin 1 → EuclideanSpace ℝ (Fin 1), ‖u 0‖ = 1 := by
  obtain ⟨u, hu, _⟩ := nikolov2013VectorColoringBound_holds 0 1 (by decide) 0
    (columnAdmissible_zero 0 1)
  exact ⟨u, hu 0⟩

-- A single unit column attains the bound on vector discrepancy.
example : vectorDiscrepancy (fun _ _ : Fin 1 => (1 : ℝ)) = 1 := by
  refine le_antisymm (nikolov2013VectorDiscrepancyUpperBound_holds 1 1 le_rfl _
    columnAdmissible_unit) (le_vectorDiscrepancy _ _ fun u hu => ?_)
  simp [hu]

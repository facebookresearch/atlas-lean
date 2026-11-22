/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.RankOneMatrix

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Quantum.RankOneMatrix

/-- The zero matrix has vanishing minors, so the equivalence puts it in product form. -/
example : ∃ a : Fin 2 → ℂ, ∃ b : Fin 2 → ℂ,
    ∀ i j, (0 : Fin 2 → Fin 2 → ℂ) i j = a i * b j :=
  (product_iff_minors _).mpr fun _ _ _ _ => by simp

/-- A nonzero product `![1, 2] ⊗ ![1, 2]` has vanishing minors. -/
example : ∀ i₁ i₂ j₁ j₂,
    (![![1, 2], ![2, 4]] : Fin 2 → Fin 2 → ℂ) i₁ j₁ * ![![1, 2], ![2, 4]] i₂ j₂ =
      ![![1, 2], ![2, 4]] i₁ j₂ * ![![1, 2], ![2, 4]] i₂ j₁ :=
  (product_iff_minors _).mp ⟨![1, 2], ![1, 2], by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num⟩

/-- A nonzero matrix with vanishing minors factors as a product. -/
example : ∃ a : Fin 2 → ℂ, ∃ b : Fin 2 → ℂ,
    ∀ i j, (![![0, 3], ![0, 6]] : Fin 2 → Fin 2 → ℂ) i j = a i * b j :=
  (product_iff_minors _).mpr fun i₁ i₂ j₁ j₂ => by
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;> norm_num

/-- The identity matrix is not in product form: its minor `1 * 1 - 0 * 0` is nonzero. -/
example : ¬ ∃ a : Fin 2 → ℂ, ∃ b : Fin 2 → ℂ,
    ∀ i j, (![![1, 0], ![0, 1]] : Fin 2 → Fin 2 → ℂ) i j = a i * b j := by
  intro h
  have hminor := (product_iff_minors _).mp h 0 1 0 1
  norm_num at hminor

/-- A product matrix has rank at most one. -/
example : (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℂ).rank ≤ 1 :=
  (rank_le_one_iff_product _).mpr ⟨![1, 2], ![1, 2], by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num⟩

/-- The `2 × 2` identity matrix has rank greater than one, by both characterizations. -/
example : ¬ (1 : Matrix (Fin 2) (Fin 2) ℂ).rank ≤ 1 := by
  intro h
  have hminor := (product_iff_minors _).mp ((rank_le_one_iff_product _).mp h) 0 1 0 1
  norm_num at hminor

end

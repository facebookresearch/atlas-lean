/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.Plotkin

open MathlibExt.Combinatorics.Coding.Plotkin

/-- Boundary check: length `1`, distance `1`, the full code
`{0, 1}` attains the Plotkin bound `2`. -/
example : ((Finset.univ : Finset (Fin 1 → Fin 2)).card : ℝ) ≤ 2 * 1 / (2 * 1 - 1) := by
  have h := plotkin_bound (n := 1) (d := 1) (by norm_num) Finset.univ (by
    intro x _ y _ hxy
    show (1 : ℕ) ≤ (Finset.univ.filter fun i => x i ≠ y i).card
    have hne : x 0 ≠ y 0 := fun h => hxy (funext fun i => by rw [Fin.eq_zero i, h])
    have hmem : (0 : Fin 1) ∈ Finset.univ.filter (fun i => x i ≠ y i) := by
      simp [hne]
    exact Finset.one_le_card.mpr ⟨0, hmem⟩)
  simpa using h

/-- The empty code trivially satisfies the bound. -/
example {n d : ℕ} (hd : n < 2 * d) :
    ((∅ : Finset (Fin n → Fin 2)).card : ℝ) ≤ 2 * d / (2 * d - n) :=
  plotkin_bound hd ∅ (fun x hx => by simp at hx)

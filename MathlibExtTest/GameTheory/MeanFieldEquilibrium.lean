/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MeanFieldEquilibrium

@[expose] public section

open Finset MathlibExt.GameTheory.MeanFieldEquilibrium

namespace MathlibExtTest.GameTheory.MeanFieldEquilibrium

/-- Crowd aversion on two states: the cost of a state is the mass of players in it. -/
def crowd : (Fin 2 → ℝ) → Fin 2 → ℝ := fun m y => m y

/-- The uniform distribution is a mean field equilibrium of crowd aversion (both states cost
`1/2`), via the support characterisation. -/
example : IsMeanFieldEquilibrium crowd (fun _ => 1 / 2) := by
  rw [isMeanFieldEquilibrium_iff]
  refine ⟨⟨fun _ => by norm_num, by simp⟩, fun _ _ _ => le_rfl⟩

/-- Crowd aversion satisfies the Lasry–Lions strict monotonicity condition
(`∑ (m₁ - m₂)² > 0` for `m₁ ≠ m₂`), so the hypotheses of `eq_of_isMeanFieldEquilibrium` are
jointly satisfiable and the uniform distribution is the unique equilibrium. -/
example (m : Fin 2 → ℝ) (hm : IsMeanFieldEquilibrium crowd m) : m = fun _ => 1 / 2 := by
  refine eq_of_isMeanFieldEquilibrium (fun m₁ m₂ _ _ hne => ?_) hm ?_
  · obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
    have hpos : 0 < (m₁ y - m₂ y) * (m₁ y - m₂ y) := mul_self_pos.2 (sub_ne_zero.2 hy)
    calc 0 < (m₁ y - m₂ y) * (m₁ y - m₂ y) := hpos
      _ ≤ ∑ z, (crowd m₁ z - crowd m₂ z) * (m₁ z - m₂ z) :=
        single_le_sum (f := fun z => (m₁ z - m₂ z) * (m₁ z - m₂ z))
          (fun z _ => mul_self_nonneg _) (mem_univ y)
  · rw [isMeanFieldEquilibrium_iff]
    exact ⟨⟨fun _ => by norm_num, by simp⟩, fun _ _ _ => le_rfl⟩

/-- A non-equilibrium: with the whole crowd in state `0` (cost `1`), moving to the empty state
`1` (cost `0`) is profitable. -/
example : ¬ IsMeanFieldEquilibrium crowd (Pi.single 0 1) := by
  rw [isMeanFieldEquilibrium_iff]
  rintro ⟨-, h⟩
  have := h 0 (by simp) 1
  simp [crowd] at this
  linarith

/-- Crowd aversion is `1`-Lipschitz for the `ℓ¹` distance. -/
example : ∀ m₁ m₂ : Fin 2 → ℝ, ∀ y, |crowd m₁ y - crowd m₂ y| ≤ 1 * ∑ z, |m₁ z - m₂ z| :=
  fun m₁ m₂ y => by
    rw [one_mul]
    exact single_le_sum (f := fun z => |m₁ z - m₂ z|) (fun z _ => abs_nonneg _) (mem_univ y)

/-- The Lasry–Lions identity at a numerical point of `ℝ`. -/
example : (3 - 1) / 2 * (‖(2 : ℝ)‖ ^ 2 - ‖(5 : ℝ)‖ ^ 2) -
      inner ℝ ((2 : ℝ) - 5) ((3 : ℝ) • (2 : ℝ) - (1 : ℝ) • 5) =
    -((3 + 1) / 2) * ‖(2 : ℝ) - 5‖ ^ 2 :=
  lasryLions_identity 3 1 (2 : ℝ) 5

end MathlibExtTest.GameTheory.MeanFieldEquilibrium

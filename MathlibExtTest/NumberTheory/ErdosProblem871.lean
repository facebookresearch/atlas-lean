/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem871

/-! # Tests for `MathlibExt.NumberTheory.ErdosProblem871` -/

namespace MathlibExtTest.ErdosProblem871

open Filter MathlibExt.NumberTheory.ErdosProblem871Wanted

-- The companion proposition follows directly from the theorem.
example : disprovedForm := conjecture_refuted

-- In a partition of the counterexample, if the first part is a basis, the second misses
-- arbitrarily large sums.
example : ∃ A : Set ℕ,
    (∀ᶠ n in atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
    (∀ t, ∀ᶠ n in atTop, ∃ pairs : Finset (ℕ × ℕ), pairs.card ≥ t ∧
      ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) ∧
    ∀ B C : Set ℕ, (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) → Disjoint B C →
      (∀ᶠ n in atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) →
      ¬ ∀ᶠ n in atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n := by
  by_contra h
  refine conjecture_refuted fun A hA => ?_
  by_contra hne
  exact h ⟨A, hA.1, hA.2, fun B C h1 h2 h3 h4 => hne ⟨B, C, h1, h2, h3, h4⟩⟩

-- The hypotheses of the conjecture are not vacuous: the set of all natural numbers satisfies
-- them, with the representations `i + (n - i)` for `i < t`.
example : (∀ᶠ n in atTop, ∃ a ∈ (Set.univ : Set ℕ), ∃ b ∈ (Set.univ : Set ℕ), a + b = n) ∧
    (∀ t, ∀ᶠ n in atTop, ∃ pairs : Finset (ℕ × ℕ), pairs.card ≥ t ∧
      ∀ p ∈ pairs, p.1 ∈ (Set.univ : Set ℕ) ∧ p.2 ∈ (Set.univ : Set ℕ) ∧ p.1 + p.2 = n ∧
        p.1 ≤ p.2) := by
  refine ⟨Eventually.of_forall fun n => ⟨0, trivial, n, trivial, Nat.zero_add n⟩, fun t => ?_⟩
  rw [eventually_atTop]
  refine ⟨2 * t, fun n hn => ⟨(Finset.range t).image fun i => (i, n - i), ?_, ?_⟩⟩
  · rw [Finset.card_image_of_injective _ fun i j h => (Prod.ext_iff.mp h).1]
    simp
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_range] at hi
    exact ⟨trivial, trivial, by dsimp only; omega, by dsimp only; omega⟩

end MathlibExtTest.ErdosProblem871

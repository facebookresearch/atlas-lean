/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SmoothPrimeGaps

/-!
# Tests for difference smoothness

The admissible pair `{-1, 1}` has absolute difference two, attaining the
lower bound for a two-element set. At size zero, the existence theorem gives
the empty set with both required properties.
-/

open MetaMathlibExt

example : ¬ IsDifferenceSmooth 1 {(-1 : ℤ), 1} := by
  apply not_isDifferenceSmooth_of_isAdmissibleFinset _ (by decide) _ 2 Nat.prime_two (by decide)
    1 (by decide)
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨0, by simp⟩

example : IsDifferenceSmooth 2 {(-1 : ℤ), 1} := by
  have htwo : 2 ∈ Nat.smoothNumbers 3 := Nat.mem_smoothNumbers_of_lt (by decide) (by decide)
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | contradiction | exact htwo

example : IsAdmissibleFinset ∅ ∧ IsDifferenceSmooth 0 ∅ := by
  obtain ⟨H, hcard, hadm, hsmooth⟩ := exists_admissible_differenceSmooth 0
  obtain rfl := Finset.card_eq_zero.mp hcard
  exact ⟨hadm, hsmooth⟩

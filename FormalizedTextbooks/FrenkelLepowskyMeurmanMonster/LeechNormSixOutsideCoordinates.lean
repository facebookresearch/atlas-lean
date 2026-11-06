/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairShapes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairCountTypes

/-! Actual outside coordinates needed to reduce norm-six vectors through the genuine Xi action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A coordinate magnitude occurring more often than an excluded set has a genuine outside
coordinate, with no catalogue or orbit assumption. -/
theorem leechNormSix_magnitude_outside (u : Fin 24 → ℤ) (k : Fin 9)
    (s : Finset (Fin 24)) (h : s.card < leechNormEightMultiplicity u k) :
    ∃ i : Fin 24, i ∉ s ∧ (u i).natAbs = k.val := by
  classical
  by_contra hn
  push Not at hn
  have hc : leechNormEightMultiplicity u k ≤ s.card := by
    apply Finset.card_le_card
    intro i hi
    have hv := (Finset.mem_filter.mp hi).2
    by_contra hs
    exact hn i hs hv
  omega

/-- Every even paired norm-six family has both a magnitude-two and a zero coordinate outside
the two root coordinates. -/
theorem leechNormSixPair_even_outside (u : LeechNormSixPair) (s : Fin 4)
    (hs : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts s)
    (he : s = 0 ∨ s = 1) :
    ∃ i j : Fin 24, i ≠ 0 ∧ i ≠ 1 ∧ j ≠ 0 ∧ j ≠ 1 ∧ i ≠ j ∧
      (u.val.val i).natAbs = 2 ∧ u.val.val j = 0 := by
  have hcount (k : Fin 9) (hk : k = 0 ∨ k = 2) :
      ({0, 1} : Finset (Fin 24)).card < leechNormEightMultiplicity u.val.val k := by
    rw [hs]
    rcases he with he | he <;> rcases hk with hk | hk <;> subst s <;> subst k <;>
      decide +kernel
  obtain ⟨i, hi, hival⟩ := leechNormSix_magnitude_outside u.val.val 2 {0, 1}
    (hcount 2 (Or.inr rfl))
  obtain ⟨j, hj, hjval⟩ := leechNormSix_magnitude_outside u.val.val 0 {0, 1}
    (hcount 0 (Or.inl rfl))
  have hi' : i ≠ 0 ∧ i ≠ 1 := by simpa using hi
  have hj' : j ≠ 0 ∧ j ≠ 1 := by simpa using hj
  have hij : i ≠ j := by intro h; subst j; omega
  exact ⟨i, j, hi'.1, hi'.2, hj'.1, hj'.2, hij, hival, Int.natAbs_eq_zero.mp hjval⟩

/-- Every odd five-coordinate paired vector has two distinct magnitude-one coordinates
outside the fixed root pair. -/
theorem leechNormSixPair_odd_five_outside (u : LeechNormSixPair)
    (hs : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 2) :
    ∃ i j : Fin 24, i ≠ 0 ∧ i ≠ 1 ∧ j ≠ 0 ∧ j ≠ 1 ∧ i ≠ j ∧
      (u.val.val i).natAbs = 1 ∧ (u.val.val j).natAbs = 1 := by
  have hc : leechNormEightMultiplicity u.val.val 1 = 23 := by rw [hs]; rfl
  obtain ⟨i, hi, hival⟩ := leechNormSix_magnitude_outside u.val.val 1 {0, 1}
    (by rw [hc]; decide +kernel)
  have hi' : i ≠ 0 ∧ i ≠ 1 := by simpa using hi
  obtain ⟨j, hj, hjval⟩ := leechNormSix_magnitude_outside u.val.val 1 {0, 1, i}
    (by rw [hc]; simp [Ne.symm hi'.1, Ne.symm hi'.2])
  have hj' : j ≠ 0 ∧ j ≠ 1 ∧ j ≠ i := by simpa [and_assoc] using hj
  exact ⟨i, j, hi'.1, hi'.2, hj'.1, hj'.2.1, Ne.symm hj'.2.2, hival, hjval⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

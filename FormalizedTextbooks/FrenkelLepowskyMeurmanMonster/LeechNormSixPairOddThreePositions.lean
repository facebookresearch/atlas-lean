/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairOddThreeOrbits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairShapes

/-! The two genuine outside high coordinates of every odd three-coordinate paired vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original odd three-coordinate multiplicities determine two distinct high coordinates
outside its high and low root coordinates. -/
theorem leechNormSixPair_odd_three_positions (u : LeechNormSixPair)
    (hs : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 3)
    (r s : Fin 24) (hr : (u.val.val r).natAbs = 3) (hslow : (u.val.val s).natAbs = 1) :
    ∃ i j : Fin 24, i ≠ r ∧ i ≠ s ∧ j ≠ r ∧ j ≠ s ∧ i ≠ j ∧
      ∀ x, (u.val.val x).natAbs = if x = r ∨ x = i ∨ x = j then 3 else 1 := by
  classical
  let f := Finset.univ.filter fun x => (u.val.val x).natAbs = 3
  have hc : f.card = 3 := by
    change leechNormEightMultiplicity u.val.val 3 = 3
    rw [hs]
    rfl
  have hrmem : r ∈ f := by simp [f, hr]
  have hsnot : s ∉ f := by simp [f, hslow]
  have he : (f.erase r).card = 2 := by rw [Finset.card_erase_of_mem hrmem, hc]
  obtain ⟨i, j, hij, heq⟩ := Finset.card_eq_two.mp he
  have hi : i ∈ f.erase r := by rw [heq]; simp
  have hj : j ∈ f.erase r := by rw [heq]; simp
  have hi' := Finset.mem_erase.mp hi
  have hj' := Finset.mem_erase.mp hj
  have his : i ≠ s := by intro h; subst i; exact hsnot hi'.2
  have hjs : j ≠ s := by intro h; subst j; exact hsnot hj'.2
  have hfull : f = insert r {i, j} := by
    rw [← heq]
    exact (Finset.insert_erase hrmem).symm
  refine ⟨i, j, hi'.1, his, hj'.1, hjs, hij, ?_⟩
  intro x
  have ha := leechNormSix_coordinate_allowed u.val.val 3
    (fun y => (leechNormSix_natAbs_le _ u.property.1 y).trans (by decide)) hs x
  change (u.val.val x).natAbs = 1 ∨ (u.val.val x).natAbs = 3 at ha
  have hmem : x ∈ f ↔ x = r ∨ x = i ∨ x = j := by simp [hfull]
  by_cases hx : x = r ∨ x = i ∨ x = j
  · have h3 : (u.val.val x).natAbs = 3 := (Finset.mem_filter.mp (hmem.mpr hx)).2
    simp [hx, h3]
  · rcases ha with ha | ha
    · simp [hx, ha]
    · have hm : x ∈ f := by simp [f, ha]
      exact False.elim (hx (hmem.mp hm))

/-- The entire odd three-coordinate catalogue in the first root orientation is genuinely
transitive, with its outside positions derived from the original lattice conditions. -/
theorem leechNormSixPair_odd_three_positive_transitive (u v : LeechNormSixPair)
    (hu : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 3)
    (hv : leechNormEightMultiplicity v.val.val = leechNormSixShapeCounts 3)
    (hu0 : u.val.val 0 = 3) (hu1 : u.val.val 1 = 1)
    (hv0 : v.val.val 0 = 3) (hv1 : v.val.val 1 = 1) :
    ∃ e : leechRootedA2PositiveRootSubgroup, e • u = v := by
  obtain ⟨i, j, hi0, hi1, hj0, hj1, hij, hupos⟩ :=
    leechNormSixPair_odd_three_positions u hu 0 1 (by rw [hu0]; rfl) (by rw [hu1]; rfl)
  obtain ⟨k, l, hk0, hk1, hl0, hl1, hkl, hvpos⟩ :=
    leechNormSixPair_odd_three_positions v hv 0 1 (by rw [hv0]; rfl) (by rw [hv1]; rfl)
  exact leechNormSixPair_odd_three_oriented_transport u v i j k l
    hi0 hi1 hj0 hj1 hij hk0 hk1 hl0 hl1 hkl hu0 hu1 hv0 hv1 hupos hvpos

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairOddMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairShapes

/-! Actual transitivity on the full odd five-coordinate family, including both root orientations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine Golay automorphism interchanges the two root coordinates. -/
theorem leechNormSixPair_root_swap_exists :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 1 ∧ p.val 1 = 0 := by
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive ![0, 1, 2, 3] ![1, 0, 2, 3]
    (by decide +kernel) (by decide +kernel)
  exact ⟨p, by simpa using hp 0, by simpa using hp 1⟩

/-- The singleton high coordinate of an actual odd five-coordinate vector determines all
coordinate magnitudes. -/
theorem leechNormSixPair_odd_five_magnitudes (u : LeechNormSixPair)
    (hs : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 2)
    (r : Fin 24) (hr : (u.val.val r).natAbs = 5) :
    ∀ i, (u.val.val i).natAbs = if i = r then 5 else 1 := by
  classical
  have hc : (Finset.univ.filter fun i => (u.val.val i).natAbs = 5).card = 1 := by
    change leechNormEightMultiplicity u.val.val 5 = 1
    rw [hs]
    rfl
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
  have hrj : r = j := by
    have hm : r ∈ Finset.univ.filter fun i => (u.val.val i).natAbs = 5 := by simp [hr]
    rw [hj] at hm
    simpa using hm
  rw [← hrj] at hj
  intro i
  by_cases hi : i = r
  · simpa [hi] using hr
  · have ha := leechNormSix_coordinate_allowed u.val.val 2
      (fun x => (leechNormSix_natAbs_le _ u.property.1 x).trans (by decide)) hs i
    change (u.val.val i).natAbs = 1 ∨ (u.val.val i).natAbs = 5 at ha
    rcases ha with ha | ha
    · simpa [hi] using ha
    · have hm : i ∈ Finset.univ.filter fun i => (u.val.val i).natAbs = 5 := by simp [ha]
      rw [hj] at hm
      exact False.elim (hi (by simpa using hm))

/-- The actual odd five-coordinate catalogue has precisely its two forced root orientations. -/
theorem leechNormSixPair_odd_five_root_pattern (u : LeechNormSixPair)
    (hs : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 2) :
    (u.val.val 0 = 5 ∧ u.val.val 1 = -1) ∨
      (u.val.val 0 = -1 ∧ u.val.val 1 = 5) := by
  obtain ⟨s, hshape, hpat⟩ := leechNormSix_pair_catalog u.val u.property.1 0 1 u.property.2
  have hs2 : s = 2 := by
    have h5 : leechNormSixShapeCounts s 5 = 1 := by
      simpa [leechNormSixShapeCounts] using congrFun (hshape.symm.trans hs) 5
    fin_cases s <;> simp_all [leechNormSixShapeCounts]
  subst s
  exact hpat

/-- A genuine root-pair swap joins the two orientations of the odd five-coordinate family. -/
theorem leechNormSixPair_odd_five_reverse_transport (u v : LeechNormSixPair)
    (hu0 : u.val.val 0 = -1) (hu1 : u.val.val 1 = 5)
    (hv0 : v.val.val 0 = 5) (hv1 : v.val.val 1 = -1)
    (hu : ∀ i, (u.val.val i).natAbs = if i = 1 then 5 else 1)
    (hv : ∀ i, (v.val.val i).natAbs = if i = 0 then 5 else 1) :
    ∃ e : leechRootedA2PositiveRootSubgroup, e • u = v := by
  obtain ⟨p, hp0, hp1⟩ := leechNormSixPair_root_swap_exists
  apply leechNormSixPair_odd_monomial_transport u v p (Or.inr ⟨hp0, hp1⟩)
  · rw [hv0]; decide
  · rw [hv0]; norm_num
  · rw [hv1]; norm_num
  · have hs : p.val.symm 0 = 1 := p.val.symm_apply_eq.mpr hp1.symm
    rw [hs, hu1, hv0]
  · have hs : p.val.symm 1 = 0 := p.val.symm_apply_eq.mpr hp0.symm
    rw [hs, hu0, hv1]
  · intro i
    have hpi : p.val i = 0 ↔ i = 1 := by
      calc
        p.val i = 0 ↔ p.val i = p.val 1 := by rw [hp1]
        _ ↔ i = 1 := p.val.injective.eq_iff
    rw [hu, hv]
    simp only [hpi]

/-- The entire actual odd five-coordinate family is one positive-root stabilizer orbit. -/
theorem leechNormSixPair_odd_five_transitive (u v : LeechNormSixPair)
    (hu : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 2)
    (hv : leechNormEightMultiplicity v.val.val = leechNormSixShapeCounts 2) :
    ∃ e : leechRootedA2PositiveRootSubgroup, e • u = v := by
  rcases leechNormSixPair_odd_five_root_pattern u hu with ⟨hu0, hu1⟩ | ⟨hu0, hu1⟩ <;>
    rcases leechNormSixPair_odd_five_root_pattern v hv with ⟨hv0, hv1⟩ | ⟨hv0, hv1⟩
  · exact leechNormSixPair_odd_five_oriented_transport u v hu0 hu1 hv0 hv1
      (leechNormSixPair_odd_five_magnitudes u hu 0 (by rw [hu0]; rfl))
      (leechNormSixPair_odd_five_magnitudes v hv 0 (by rw [hv0]; rfl))
  · obtain ⟨e, he⟩ := leechNormSixPair_odd_five_reverse_transport v u hv0 hv1 hu0 hu1
      (leechNormSixPair_odd_five_magnitudes v hv 1 (by rw [hv1]; rfl))
      (leechNormSixPair_odd_five_magnitudes u hu 0 (by rw [hu0]; rfl))
    exact ⟨e⁻¹, by
      have h := congrArg (fun w : LeechNormSixPair => e⁻¹ • w) he
      simpa only [inv_smul_smul] using h.symm⟩
  · exact leechNormSixPair_odd_five_reverse_transport u v hu0 hu1 hv0 hv1
      (leechNormSixPair_odd_five_magnitudes u hu 1 (by rw [hu1]; rfl))
      (leechNormSixPair_odd_five_magnitudes v hv 0 (by rw [hv0]; rfl))
  · apply leechNormSixPair_odd_sign_transport u v
    · rw [hu0]; decide
    · rw [hv0]; decide
    · rw [hu0]; norm_num
    · rw [hu1]; norm_num
    · exact hu0.trans hv0.symm
    · exact hu1.trans hv1.symm
    · intro i
      exact (leechNormSixPair_odd_five_magnitudes u hu 1 (by rw [hu1]; rfl) i).trans
        (leechNormSixPair_odd_five_magnitudes v hv 1 (by rw [hv1]; rfl) i).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

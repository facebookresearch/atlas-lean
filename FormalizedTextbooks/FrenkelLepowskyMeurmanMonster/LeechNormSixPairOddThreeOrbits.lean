/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairOddMonomial

/-! Actual transitivity on the odd three-coordinate family with its fixed root orientation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine root-pair point stabilizer transports every ordered pair of outside coordinates. -/
theorem leechNormSixPair_outside_pair_transport (i j k l : Fin 24)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hij : i ≠ j)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hl0 : l ≠ 0) (hl1 : l ≠ 1) (hkl : k ≠ l) :
    ∃ p : golayAutomorphismSubgroup,
      p.val 0 = 0 ∧ p.val 1 = 1 ∧ p.val i = k ∧ p.val j = l := by
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive ![0, 1, i, j] ![0, 1, k, l]
    (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
    (by intro a b h; fin_cases a <;> fin_cases b <;> simp_all)
  exact ⟨p, by simpa using hp 0, by simpa using hp 1,
    by simpa using hp 2, by simpa using hp 3⟩

/-- All actual odd three-coordinate vectors with the same root orientation lie in one genuine
positive-root stabilizer orbit; the outside positions and all original signs may vary. -/
theorem leechNormSixPair_odd_three_oriented_transport (u v : LeechNormSixPair)
    (i j k l : Fin 24)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hij : i ≠ j)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hl0 : l ≠ 0) (hl1 : l ≠ 1) (hkl : k ≠ l)
    (hu0 : u.val.val 0 = 3) (hu1 : u.val.val 1 = 1)
    (hv0 : v.val.val 0 = 3) (hv1 : v.val.val 1 = 1)
    (hu : ∀ x, (u.val.val x).natAbs = if x = 0 ∨ x = i ∨ x = j then 3 else 1)
    (hv : ∀ x, (v.val.val x).natAbs = if x = 0 ∨ x = k ∨ x = l then 3 else 1) :
    ∃ e : leechRootedA2PositiveRootSubgroup, e • u = v := by
  obtain ⟨p, hp0, hp1, hpi, hpj⟩ := leechNormSixPair_outside_pair_transport
    i j k l hi0 hi1 hj0 hj1 hij hk0 hk1 hl0 hl1 hkl
  apply leechNormSixPair_odd_monomial_transport u v p (Or.inl ⟨hp0, hp1⟩)
  · rw [hv0]; decide
  · rw [hv0]; norm_num
  · rw [hv1]; norm_num
  · have hs : p.val.symm 0 = 0 := p.val.symm_apply_eq.mpr hp0.symm
    rw [hs, hu0, hv0]
  · have hs : p.val.symm 1 = 1 := p.val.symm_apply_eq.mpr hp1.symm
    rw [hs, hu1, hv1]
  · intro x
    have hpx0 : p.val x = 0 ↔ x = 0 := by
      calc
        p.val x = 0 ↔ p.val x = p.val 0 := by rw [hp0]
        _ ↔ x = 0 := p.val.injective.eq_iff
    have hpxi : p.val x = k ↔ x = i := by
      calc
        p.val x = k ↔ p.val x = p.val i := by rw [hpi]
        _ ↔ x = i := p.val.injective.eq_iff
    have hpxj : p.val x = l ↔ x = j := by
      calc
        p.val x = l ↔ p.val x = p.val j := by rw [hpj]
        _ ↔ x = j := p.val.injective.eq_iff
    rw [hu, hv]
    simp only [hpx0, hpxi, hpxj]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

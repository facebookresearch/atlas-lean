/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairOddSigns

/-! Actual monomial transports for the odd families in the paired norm-six catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine coordinate permutation preserving the root pair fixes its positive sum. -/
theorem leechNormSixPair_permutation_root (p : golayAutomorphismSubgroup)
    (hp : (p.val 0 = 0 ∧ p.val 1 = 1) ∨ (p.val 0 = 1 ∧ p.val 1 = 0)) :
    leechIntegralAction (golayPermutationIsometry p) leechRootedA2Root =
      leechRootedA2Root := by
  rcases hp with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact leechRootedA2Root_permutation p h0 h1
  · exact leechRootedA2Root_permutation_swap p h0 h1

/-- A genuine Golay coordinate transport and the forced odd signs give a full actual transport
inside the positive-root stabilizer. -/
theorem leechNormSixPair_odd_monomial_transport (u v : LeechNormSixPair)
    (p : golayAutomorphismSubgroup)
    (hp : (p.val 0 = 0 ∧ p.val 1 = 1) ∨ (p.val 0 = 1 ∧ p.val 1 = 0))
    (hv : Odd (v.val.val 0)) (hn0 : v.val.val 0 ≠ 0) (hn1 : v.val.val 1 ≠ 0)
    (h0 : u.val.val (p.val.symm 0) = v.val.val 0)
    (h1 : u.val.val (p.val.symm 1) = v.val.val 1)
    (habs : ∀ i, (u.val.val i).natAbs = (v.val.val (p.val i)).natAbs) :
    ∃ e : leechRootedA2PositiveRootSubgroup, e • u = v := by
  have hr := leechNormSixPair_permutation_root p hp
  let a : leechRootedA2PositiveRootSubgroup :=
    ⟨⟨golayPermutationIsometry p,
      (leechRootedA2RootLineSubgroup_mem _).mpr (Or.inl hr)⟩, hr⟩
  have ha (i : Fin 24) : (a • u).val.val i = u.val.val (p.val.symm i) := by
    rw [leechNormSixPair_smul_val, leechIntegralAction_golayPermutation]
    rfl
  have ha0 : (a • u).val.val 0 = v.val.val 0 := (ha 0).trans h0
  have ha1 : (a • u).val.val 1 = v.val.val 1 := (ha 1).trans h1
  obtain ⟨b, hb⟩ := leechNormSixPair_odd_sign_transport (a • u) v
    (ha0.symm ▸ hv) hv (ha0.symm ▸ hn0) (ha1.symm ▸ hn1) ha0 ha1 (by
      intro i
      rw [ha]
      simpa only [p.val.apply_symm_apply] using habs (p.val.symm i))
  exact ⟨b * a, by simpa only [mul_smul] using hb⟩

/-- Within the oriented odd five-coordinate family, the full actual vectors are related. -/
theorem leechNormSixPair_odd_five_oriented_transport (u v : LeechNormSixPair)
    (hu0 : u.val.val 0 = 5) (hu1 : u.val.val 1 = -1)
    (hv0 : v.val.val 0 = 5) (hv1 : v.val.val 1 = -1)
    (hu : ∀ i, (u.val.val i).natAbs = if i = 0 then 5 else 1)
    (hv : ∀ i, (v.val.val i).natAbs = if i = 0 then 5 else 1) :
    ∃ e : leechRootedA2PositiveRootSubgroup, e • u = v := by
  apply leechNormSixPair_odd_sign_transport u v
  · rw [hu0]; decide
  · rw [hv0]; decide
  · rw [hu0]; norm_num
  · rw [hu1]; norm_num
  · exact hu0.trans hv0.symm
  · exact hu1.trans hv1.symm
  · intro i
    exact (hu i).trans (hv i).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

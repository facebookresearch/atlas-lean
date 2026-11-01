/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthMonomialSubgroup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderSigns

/-! Exact order of the actual constructed sixth flag monomial subgroup in the Conway quotient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both actual lattice signs belong to the constructed equal-sign flag monomial subgroup. -/
theorem leechRootedA2SixthMonomialSubgroup_signs :
    signsSubgroup ≤ leechRootedA2SixthMonomialSubgroup := by
  intro g hg
  rcases hg with hg | hg
  · have h : g = 1 := Subtype.ext hg
    rw [h]
    exact leechRootedA2SixthMonomialSubgroup.one_mem
  · let c : golayCode := golayEncoder.rangeRestrict (Pi.single 11 1)
    have hc : c.val = fun _ => 1 := golay_all_one
    let d : leechRootedA2SixthSignSpace := ⟨c, by
      change c.val 17 = c.val 16 ∧ c.val 19 = c.val 16
      rw [hc]
      exact ⟨rfl, rfl⟩⟩
    refine ⟨d, 1, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext i
    change g.val x i = qSign (c.val i) * x i
    rw [hg x, hc, qSign_one]
    simp only [Pi.neg_apply, neg_one_mul]

/-- The central-sign image of the actual constructed flag monomial subgroup. -/
def leechRootedA2SixthMonomialCo1Subgroup : Subgroup Co1 :=
  leechRootedA2SixthMonomialSubgroup.map (QuotientGroup.mk' signsSubgroup)

/-- The genuine monomial flag subgroup has index 201405204000 in Co0. -/
theorem leechRootedA2SixthMonomialSubgroup_index :
    leechRootedA2SixthMonomialSubgroup.index = 201405204000 := by
  have h := leechRootedA2SixthMonomialSubgroup.card_mul_index
  rw [leechRootedA2SixthMonomialSubgroup_card, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 41287680)
    (h.trans (by decide : 8315553613086720000 = 41287680 * 201405204000))

/-- The actual central-sign quotient preserves the original monomial flag subgroup index. -/
theorem leechRootedA2SixthMonomialCo1Subgroup_index :
    leechRootedA2SixthMonomialCo1Subgroup.index = 201405204000 := by
  change (leechRootedA2SixthMonomialSubgroup.map (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact leechRootedA2SixthMonomialSubgroup_index
  · rw [QuotientGroup.ker_mk']
    exact leechRootedA2SixthMonomialSubgroup_signs

/-- The genuine constructed sixth flag monomial subgroup has 20643840 elements in Co1. -/
theorem leechRootedA2SixthMonomialCo1Subgroup_card :
    Nat.card leechRootedA2SixthMonomialCo1Subgroup = 20643840 := by
  have h := leechRootedA2SixthMonomialCo1Subgroup.card_mul_index
  rw [leechRootedA2SixthMonomialCo1Subgroup_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 201405204000)
    (h.trans (by decide : 4157776806543360000 = 20643840 * 201405204000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

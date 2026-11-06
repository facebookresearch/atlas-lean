/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact whole-vector cancellation of the pair-short part under the ninth inverse triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthPartners
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTrialityInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private noncomputable def pairBTerm (k : Fin 240) : GriessSpace :=
  if monsterNortonLine01PairEighthIsPair k then
    ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 32) •
      trialityABCBasis 1 (monsterNortonLine01PairEighthPhysicalPair k) else 0

private theorem pairBTerm_partner (k : Fin 240) :
    pairBTerm (monsterNortonLine01PairEighthPartner k) = -pairBTerm k := by
  unfold pairBTerm
  rw [(monsterNortonLine01PairEighthPartner_certificate k).2.1]
  by_cases hk : monsterNortonLine01PairEighthIsPair k = true
  · rw [ite_eq_left hk, ite_eq_left hk,
      monsterNortonLine01PairEighthPartner_physical k hk,
      ((monsterNortonLine01PairEighthPartner_certificate k).2.2 hk).2.2]
    simp only [Int.cast_neg, neg_div, neg_smul]
  · rw [ite_eq_right hk, ite_eq_right hk, neg_zero]

/-- All 112 genuine eighth pair outputs cancel their entire B contribution after inverse extra. -/
theorem monsterNortonLine01PairNinth_pair_short_cancel :
    (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then
      ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 32) •
        trialityABCBasis 1 (monsterNortonLine01PairEighthPhysicalPair k) else 0) = 0 := by
  change (∑ k : Fin 240, pairBTerm k) = 0
  let e : Fin 240 ≃ Fin 240 := {
    toFun := monsterNortonLine01PairEighthPartner,
    invFun := monsterNortonLine01PairEighthPartner,
    left_inv := monsterNortonLine01PairEighthPartner_involutive,
    right_inv := monsterNortonLine01PairEighthPartner_involutive }
  have hn : (∑ k : Fin 240, pairBTerm k) = -(∑ k : Fin 240, pairBTerm k) := by
    calc
      _ = ∑ k : Fin 240, pairBTerm (monsterNortonLine01PairEighthPartner k) :=
        (e.sum_comp pairBTerm).symm
      _ = _ := by simp only [pairBTerm_partner, Finset.sum_neg_distrib]
  have hsum : (∑ k : Fin 240, pairBTerm k) + (∑ k : Fin 240, pairBTerm k) = 0 :=
    eq_neg_iff_add_eq_zero.mp hn
  have htwo : (2 : ℝ) • (∑ k : Fin 240, pairBTerm k) = 0 := by
    rw [two_smul, hsum]
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

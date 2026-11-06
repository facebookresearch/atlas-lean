/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual octad projections of the complete first pair-short seventh state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairOctadIndices
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortSixthCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem abc_octad_zero (s : Fin 3) (p : Fin 276) (d : Fin 759) (r : Fin 64) :
    monsterNortonShortProjection (trialityABCBasis s p) (Sum.inr (Sum.inl (d, r))) = 0 := by
  change (griessConwayEncode (trialityABCBasis s p)).2.1 (Sum.inr (Sum.inl (d, r))) = 0
  rw [griessConwayEncode_ABC_basis]

private theorem octad_projection (d a : Fin 759) (v : Fin 64 → ℝ) (r : Fin 64) :
    monsterNortonShortProjection (monsterNortonOctadShortVector d v)
      (Sum.inr (Sum.inl (a, r))) = if a = d then v r else 0 := by
  rw [monsterNortonOctadShortVector, monsterNortonShortProjection_short]
  rfl

/-- Each actual seventh term has its exact original octad Fourier row or zero contribution. -/
theorem monsterNortonLine01PairSeventhTerm_octad (e : Fin 64) (a : Fin 14) (r : Fin 64) :
    monsterNortonShortProjection (monsterNortonLine01PairSeventhTerm e)
      (Sum.inr (Sum.inl (monsterNortonLine01PairBlockOctad a, r))) =
        if monsterNortonLine01PairInverseIsPair e then 0
        else if monsterNortonLine01PairInverseOctadSlot e = a then
          trialityOctadAction (Pi.single (monsterNortonLine01PairInverseOctadSign e) 1) r
        else 0 := by
  unfold monsterNortonLine01PairSeventhTerm
  by_cases h : monsterNortonLine01PairInverseIsPair e = true
  · simp only [ite_eq_left h, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      abc_octad_zero, smul_zero, zero_add]
  · simp only [ite_eq_right h]
    rw [octad_projection]
    have hi : monsterNortonLine01PairBlockOctad a =
        monsterNortonLine01PairBlockOctad (monsterNortonLine01PairInverseOctadSlot e) ↔
          monsterNortonLine01PairInverseOctadSlot e = a := by
      rw [monsterNortonLine01PairBlockOctad_injective.eq_iff, eq_comm]
    change (if monsterNortonLine01PairBlockOctad a =
        monsterNortonLine01PairBlockOctad (monsterNortonLine01PairInverseOctadSlot e)
      then _ else _) = _
    by_cases hs : monsterNortonLine01PairInverseOctadSlot e = a
    · have hd := hi.mpr hs
      simp only [ite_eq_left hs, ite_eq_left hd]
    · have hd : ¬monsterNortonLine01PairBlockOctad a =
          monsterNortonLine01PairBlockOctad (monsterNortonLine01PairInverseOctadSlot e) := by
        intro hh
        exact hs (hi.mp hh)
      simp only [ite_eq_right hs, ite_eq_right hd]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

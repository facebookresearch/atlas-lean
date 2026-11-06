/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The entire actual matrix coordinate of the first pair-short seventh state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01MatrixSixthCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original increasing pair index attached to each reached finite output slot. -/
noncomputable def monsterNortonLine01PairInversePhysicalPair (e : Fin 64) : Fin 276 :=
  griessPairIndex (monsterNortonLine01PairInversePairFirst e)
    (monsterNortonLine01PairInversePairSecond e)
    (ne_of_lt (monsterNortonLine01PairInversePair_increasing e))

private theorem abc_zero_matrix (p : Fin 276) :
    monsterNortonMatrixProjection (trialityABCBasis 0 p) = trialityPairMatrix p := by
  change (griessConwayEncode (trialityABCBasis 0 p)).1 = _
  rw [griessConwayEncode_ABC_zero_sparse]

private theorem abc_two_matrix (p : Fin 276) :
    monsterNortonMatrixProjection (trialityABCBasis 2 p) = 0 := by
  change (griessConwayEncode (trialityABCBasis 2 p)).1 = _
  rw [griessConwayEncode_ABC_basis]
  funext i j
  by_cases h : i = j <;> simp [h]

private theorem octad_matrix_zero (d : Fin 759) (v : Fin 64 → ℝ) :
    monsterNortonMatrixProjection (monsterNortonOctadShortVector d v) = 0 := by
  change (griessConwayEncode (monsterNortonOctadShortVector d v)).1 = _
  rw [monsterNortonOctadShortVector, griessConwayEncode_decode _ (by intro i j; rfl)]

/-- Only the actual pair terms contribute their transported A matrix to the seventh state. -/
theorem monsterNortonLine01PairSeventhTerm_matrix (e : Fin 64) :
    monsterNortonMatrixProjection (monsterNortonLine01PairSeventhTerm e) =
      if monsterNortonLine01PairInverseIsPair e then
        (1 / 2 : ℝ) • trialityPairMatrix (monsterNortonLine01PairInversePhysicalPair e)
      else 0 := by
  unfold monsterNortonLine01PairSeventhTerm
  by_cases h : monsterNortonLine01PairInverseIsPair e = true
  · simp only [ite_eq_left h, map_add, map_smul, abc_zero_matrix, abc_two_matrix,
      smul_zero, add_zero]
    rfl
  · simp only [ite_eq_right h, octad_matrix_zero]

/-- The whole actual seventh matrix, retaining each complete integer source coefficient. -/
theorem monsterNortonLine01PairSeventh_matrix :
    monsterNortonMatrixProjection monsterNortonLine01PairAfterSeventh =
      ∑ e : Fin 64, if monsterNortonLine01PairInverseIsPair e then
        ((monsterNortonLine01PairSixthNumerator e : ℝ) / 16) •
          trialityPairMatrix (monsterNortonLine01PairInversePhysicalPair e)
      else 0 := by
  rw [monsterNortonLine01PairAfterSeventh, map_sum]
  simp only [map_smul, monsterNortonLine01PairSeventhTerm_matrix]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : monsterNortonLine01PairInverseIsPair e = true
  · simp only [ite_eq_left h, smul_smul]
    have hc : ((monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8 *
        qSign (monsterNortonLine01PairOctadVPhase e) *
          qSign (monsterNortonLine01PairInverseVPhase e)) * (1 / 2) =
            (monsterNortonLine01PairSixthNumerator e : ℝ) / 16 := by
      simp only [monsterNortonLine01PairSixthNumerator, Int.cast_mul,
        monsterNortonLine01PairPhaseSign_cast]
      ring
    rw [hc]
  · simp only [ite_eq_right h, smul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

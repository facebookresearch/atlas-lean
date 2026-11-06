/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual tenth forward-U binding and the resulting complete inverse-U state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairTenthV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The two surviving octad units are the whole actual U images of the two first-pair units. -/
theorem monsterNortonLine01PairSurvivor_U (a : Fin 2) :
    y555NortonActualU.val (monsterNortonPureShort
      (Sum.inl (a, monsterNortonLine01AdjacentPair 0))) =
      monsterNortonPureShort (Sum.inr (Sum.inl
        (monsterNortonLine01PairEighthBlockOctad a,
          monsterNortonLine01PairNinthOctadTarget a))) := by
  rw [← monsterNortonLine01PairEighthInput_pair a 0,
    monsterNortonLine01PairEighthU_unit]
  have hi : (⟨8 * a.val + (0 : Fin 8).val, by omega⟩ : Fin 240) =
      ⟨8 * a.val, by omega⟩ := Fin.ext (by simp)
  rw [hi, monsterNortonLine01PairSurvivor_output]

/-- The tenth literal V action has its true matrix and positive two-octad components. -/
theorem monsterNortonLine01PairTenth_actual :
    y555NortonV.val (sExtra.symm (y555NortonActualU.val monsterNortonLine01PairAfterSeventh)) =
      (-1 / 2 : ℝ) • y555NortonActualU.val
        (trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0)) +
      ∑ a : Fin 2, (1 / 2 : ℝ) • monsterNortonPureShort
        (Sum.inr (Sum.inl (monsterNortonLine01PairEighthBlockOctad a,
          monsterNortonLine01PairNinthOctadTarget a))) := by
  rw [monsterNortonLine01PairNinth_actual, map_add, map_smul,
    monsterNortonLine01PairTenthV_matrix, map_sum]
  apply congrArg (fun x : GriessSpace => (-1 / 2 : ℝ) • y555NortonActualU.val
    (trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0)) + x)
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, monsterNortonLine01PairTenthV_unit, smul_neg, ← neg_smul]
  exact congrArg (fun c : ℝ => c • monsterNortonPureShort
    (Sum.inr (Sum.inl (monsterNortonLine01PairEighthBlockOctad a,
      monsterNortonLine01PairNinthOctadTarget a)))) (by ring)

/-- The entire tenth state is exactly one forward-U image, with all original components fixed. -/
theorem monsterNortonLine01PairTenth_forward_U :
    y555NortonV.val (sExtra.symm (y555NortonActualU.val monsterNortonLine01PairAfterSeventh)) =
      y555NortonActualU.val
        ((-1 / 2 : ℝ) • trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0) +
          (1 / 2 : ℝ) • trialityABCBasis 2 (monsterNortonLine01AdjacentPair 0)) := by
  rw [monsterNortonLine01PairTenth_actual, monsterNortonPairShort_C, map_add, map_smul,
    map_smul, map_add, monsterNortonLine01PairSurvivor_U, monsterNortonLine01PairSurvivor_U,
    smul_add, Fin.sum_univ_two]

private theorem generated_inverse_apply (g : G) (x : GriessSpace) :
    (g⁻¹).val (g.val x) = x := by
  change g.val.symm (g.val x) = x
  exact LinearEquiv.symm_apply_apply _ _

/-- Literal inverse U cancels that whole actual forward image and gives the exact A,C vector. -/
theorem monsterNortonLine01PairEleventh_actual :
    (y555NortonActualU⁻¹).val (y555NortonV.val
      (sExtra.symm (y555NortonActualU.val monsterNortonLine01PairAfterSeventh))) =
      (-1 / 2 : ℝ) • trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0) +
        (1 / 2 : ℝ) • trialityABCBasis 2 (monsterNortonLine01AdjacentPair 0) := by
  rw [monsterNortonLine01PairTenth_forward_U]
  exact generated_inverse_apply y555NortonActualU _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

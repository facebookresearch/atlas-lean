/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact physical matrix pairings with whole preferred-short positive-triality packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMatrixPacketPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortPositiveTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every whole pure matrix is orthogonal to every original preferred short unit. -/
theorem monsterNortonPureMatrix_short_form (A : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, A i j = A j i) (r : GriessShortIndex) :
    griessForm (griessConwayDecode (A, (0, 0))) (monsterNortonPureShort r) = 0 := by
  rw [monsterNortonForm_pureShort_right]
  change (griessConwayEncode (griessConwayDecode (A, (0, 0)))).2.1 r = 0
  rw [griessConwayEncode_decode _ ha]
  rfl

private theorem scalar_pair_dot {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → I → ℝ) (a b : I) :
    (∑ i, ∑ j, f i j * ((if i = a ∧ j = b then 1 else 0) +
      (if i = b ∧ j = a then 1 else 0))) = f a b + f b a := by
  simp only [ite_and, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_const_zero]

/-- A pure matrix pairs with a physical A unit by twice its indicated off-diagonal entry. -/
theorem monsterNortonPureMatrix_A_form (A : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, A i j = A j i) (p : Fin 276) :
    griessForm (griessConwayDecode (A, (0, 0))) (trialityABCBasis 0 p) =
      2 * A (griessCoordinatePair p).1 (griessCoordinatePair p).2 := by
  have hA : trialityABCBasis 0 p = griessConwayDecode (trialityPairMatrix p, (0, 0)) := by
    rw [← griessConwayEncode_ABC_zero_sparse, griessConwayDecode_encode]
  rw [hA, monsterNortonForm_pure_matrix_raw A _ 0 0 ha (trialityPairMatrix_symmetric _)]
  simp_rw [trialityPairMatrix_apply]
  rw [scalar_pair_dot (fun i j => A i j)]
  rw [ha (griessCoordinatePair p).2 (griessCoordinatePair p).1]
  ring

/-- The full pair extra packet pairs with a pure matrix by its original physical pair entry. -/
theorem monsterNortonPureMatrix_pairExtra_form (A : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, A i j = A j i) (s : Fin 2) (p : Fin 276) :
    griessForm (griessConwayDecode (A, (0, 0)))
      (monsterNortonShortExtraPacket (Sum.inl (s, p))) =
        A (griessCoordinatePair p).1 (griessCoordinatePair p).2 := by
  simp only [monsterNortonShortExtraPacket, map_add, map_smul, smul_eq_mul]
  rw [monsterNortonPureMatrix_A_form A ha p, monsterNortonPairShort_C]
  simp only [map_add, monsterNortonPureMatrix_short_form A ha, add_zero, mul_zero]
  ring

/-- The entire actual octad extra packet is orthogonal to every pure matrix. -/
theorem monsterNortonPureMatrix_octadExtra_form (A : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, A i j = A j i) (d : Fin 759) (e : Fin 64) :
    griessForm (griessConwayDecode (A, (0, 0)))
      (monsterNortonShortExtraPacket (Sum.inr (Sum.inl (d, e)))) = 0 := by
  unfold monsterNortonShortExtraPacket monsterNortonOctadShortVector
  rw [monsterNortonForm_pure_matrix_raw A 0 _ 0 ha (by intros; rfl)]
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

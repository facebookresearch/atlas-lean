/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact pair-matrix and signed-short products on Y and Z. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairMatrixRelations

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Spatial row exchange on the signed Y basis carries exactly the pair character. -/
theorem trialityYTensor_row_swap (p : Fin 276) (d : Fin 2048) (j : Fin 24)
    (t : SpinIndex) (i : Fin 24) :
    (if i = (griessCoordinatePair p).1 then
        trialityYTensor d j t (griessCoordinatePair p).2 else 0) +
      (if i = (griessCoordinatePair p).2 then
        trialityYTensor d j t (griessCoordinatePair p).1 else 0) =
    qSign (golayBooleanCast ((golayEncodedMask d.val).testBit
        (griessCoordinatePair p).1.val) +
      golayBooleanCast ((golayEncodedMask d.val).testBit
        (griessCoordinatePair p).2.val)) *
      ((if j = (griessCoordinatePair p).1 then
          trialityYTensor d (griessCoordinatePair p).2 t i else 0) +
        (if j = (griessCoordinatePair p).2 then
          trialityYTensor d (griessCoordinatePair p).1 t i else 0)) := by
  rw [qSign_boolean_add]
  have hn := griessCoordinatePair_ne p
  by_cases hj1 : j = (griessCoordinatePair p).1
  · subst j
    by_cases hi : i = (griessCoordinatePair p).2
    · subst i
      by_cases hs : spinDictionaryCode t = d
      all_goals
        cases ha : (golayEncodedMask d.val).testBit (griessCoordinatePair p).1.val <;>
          cases hb : (golayEncodedMask d.val).testBit (griessCoordinatePair p).2.val <;>
          simp [trialityYTensor, hn, hn.symm, hs, ha, hb] <;> ring
    · simp [trialityYTensor, hn, hn.symm, hi]
  · by_cases hj2 : j = (griessCoordinatePair p).2
    · subst j
      by_cases hi : i = (griessCoordinatePair p).1
      · subst i
        by_cases hs : spinDictionaryCode t = d
        all_goals
          cases ha : (golayEncodedMask d.val).testBit (griessCoordinatePair p).1.val <;>
            cases hb : (golayEncodedMask d.val).testBit (griessCoordinatePair p).2.val <;>
            simp [trialityYTensor, hn, hn.symm, hs, ha, hb] <;> ring
      · simp [trialityYTensor, hn, hn.symm, hi]
    · have hj1' := Ne.symm hj1
      have hj2' := Ne.symm hj2
      simp [trialityYTensor, hj1, hj2, hj1', hj2']

/-- Spatial row exchange on Z has no extra spatial sign. -/
theorem trialityZTensor_row_swap (p : Fin 276) (d : Fin 2048) (j : Fin 24)
    (t : SpinIndex) (i : Fin 24) :
    (if i = (griessCoordinatePair p).1 then
        trialityZTensor d j t (griessCoordinatePair p).2 else 0) +
      (if i = (griessCoordinatePair p).2 then
        trialityZTensor d j t (griessCoordinatePair p).1 else 0) =
      (if j = (griessCoordinatePair p).1 then
        trialityZTensor d (griessCoordinatePair p).2 t i else 0) +
      (if j = (griessCoordinatePair p).2 then
        trialityZTensor d (griessCoordinatePair p).1 t i else 0) := by
  have hn := griessCoordinatePair_ne p
  by_cases hi1 : i = (griessCoordinatePair p).1 <;>
    by_cases hi2 : i = (griessCoordinatePair p).2 <;>
    by_cases hj1 : j = (griessCoordinatePair p).1 <;>
    by_cases hj2 : j = (griessCoordinatePair p).2 <;>
      simp_all [trialityZTensor, eq_comm]

/-- On an all-one-even tensor, B acts by the elementary spatial row exchange. -/
theorem trialityPairB_raw_tensor_even (p : Fin 276) (T : SpinIndex → Fin 24 → ℝ)
    (heven : ∀ t i, T (t + Pi.single 11 1) i = T t i) (t : SpinIndex) (i : Fin 24) :
    (conwayRawProduct (0, (trialityPairBShort p, 0)) (0, (0, T))).2.2 t i =
      qSign (golayEncoder t (griessCoordinatePair p).1 +
        golayEncoder t (griessCoordinatePair p).2) *
      ((if i = (griessCoordinatePair p).1 then T t (griessCoordinatePair p).2 else 0) +
        (if i = (griessCoordinatePair p).2 then T t (griessCoordinatePair p).1 else 0)) := by
  rw [trialityPairB_raw_tensor]
  simp_rw [spinOperator_griessPairMinus, spinOperator_griessPairPlus, heven]
  rw [← Finset.sum_sub_distrib]
  let c := qSign (golayEncoder t (griessCoordinatePair p).1 +
    golayEncoder t (griessCoordinatePair p).2)
  have hterm (j : Fin 24) :
      c * T t j * conwayTensorCoefficient (Sum.inl (0,p)) j i -
        c * T t j * conwayTensorCoefficient (Sum.inl (1,p)) j i =
      (8 * c) * (trialityPairMatrix p j i * T t j) := by
    have h := conwayTensorCoefficient_pair_difference p j i
    calc
      _ = c * T t j * (conwayTensorCoefficient (Sum.inl (0,p)) j i -
        conwayTensorCoefficient (Sum.inl (1,p)) j i) := by ring
      _ = _ := by rw [h]; ring
  change (∑ j, (c * T t j * conwayTensorCoefficient (Sum.inl (0,p)) j i -
    c * T t j * conwayTensorCoefficient (Sum.inl (1,p)) j i)) / 8 = _
  simp_rw [hterm]
  rw [← Finset.mul_sum, trialityPairMatrix_tensor_apply]
  change (8 * c) * _ / 8 = c * _
  ring

/-- The complete raw B×Z product has exactly its source pair character and row exchange. -/
theorem trialityPairB_raw_Z (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (0, (trialityPairBShort p, 0)) (0, (0, trialityZTensor d j)) =
      (0, (0, fun t i =>
        qSign (golayBooleanCast ((golayEncodedMask d.val).testBit
            (griessCoordinatePair p).1.val) +
          golayBooleanCast ((golayEncodedMask d.val).testBit
            (griessCoordinatePair p).2.val)) *
        ((if j = (griessCoordinatePair p).1 then
            trialityZTensor d (griessCoordinatePair p).2 t i else 0) +
          (if j = (griessCoordinatePair p).2 then
            trialityZTensor d (griessCoordinatePair p).1 t i else 0)))) := by
  apply Prod.ext
  · funext a b
    simp only [conwayRawProduct, Matrix.zero_apply, Pi.zero_apply, zero_mul, mul_zero,
      add_zero, ite_self, Finset.sum_const_zero, zero_div]
  · apply Prod.ext
    · funext r
      simp [conwayRawProduct, spinOperator, conwayShortPairing]
    · funext t i
      rw [trialityPairB_raw_tensor_even p _ (trialityZTensor_add_omega d j)]
      rw [mul_add]
      simp only [mul_ite, mul_zero]
      rw [trialityZTensor_pair_character p d j t (griessCoordinatePair p).2,
        trialityZTensor_pair_character p d j t (griessCoordinatePair p).1]
      have h := congrArg (fun z : ℝ =>
        qSign (golayBooleanCast ((golayEncodedMask d.val).testBit
            (griessCoordinatePair p).1.val) +
          golayBooleanCast ((golayEncodedMask d.val).testBit
            (griessCoordinatePair p).2.val)) * z) (trialityZTensor_row_swap p d j t i)
      simpa only [mul_add, mul_ite, mul_zero] using h

/-- The complete raw A×Y product carries the same pair character and source row exchange. -/
theorem trialityPairMatrix_raw_Y (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (trialityPairMatrix p, (0, 0)) (0, (0, trialityYTensor d j)) =
      (0, (0, fun t i =>
        qSign (golayBooleanCast ((golayEncodedMask d.val).testBit
            (griessCoordinatePair p).1.val) +
          golayBooleanCast ((golayEncodedMask d.val).testBit
            (griessCoordinatePair p).2.val)) *
        ((if j = (griessCoordinatePair p).1 then
            trialityYTensor d (griessCoordinatePair p).2 t i else 0) +
          (if j = (griessCoordinatePair p).2 then
            trialityYTensor d (griessCoordinatePair p).1 t i else 0)))) := by
  rw [trialityPairMatrix_raw_restriction]
  refine Prod.ext rfl ?_
  apply Prod.ext
  · funext r
    simp only [Pi.zero_apply, mul_zero]
  · funext t i
    exact trialityYTensor_row_swap p d j t i

/-- Exchange the two spatial source coordinates selected by a pair. -/
noncomputable def trialityXYZExchange (s : Fin 3) (p : Fin 276) (d : Fin 2048)
    (j : Fin 24) : GriessSpace :=
  (if j = (griessCoordinatePair p).1 then
      trialityXYZBasis s (finProdFinEquiv (d, (griessCoordinatePair p).2)) else 0) +
    (if j = (griessCoordinatePair p).2 then
      trialityXYZBasis s (finProdFinEquiv (d, (griessCoordinatePair p).1)) else 0)

theorem trialityXYZExchange_cycle (s : Fin 3) (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (trialityXYZExchange s p d j) =
      trialityXYZExchange (trialityCycle s) p d j := by
  simp only [trialityXYZExchange, map_add]
  have hn := griessCoordinatePair_ne p
  by_cases h1 : j = (griessCoordinatePair p).1 <;>
    by_cases h2 : j = (griessCoordinatePair p).2 <;>
      simp [h1, h2, hn, hn.symm, sExtra_XYZ_basis]

private theorem decode_tensor_smul (c : ℝ) (T : SpinIndex → Fin 24 → ℝ) :
    griessConwayDecode (0, (0, fun t i => c * T t i)) =
      c • griessConwayDecode (0, (0, T)) := by
  have h : ((0, (0, fun t i => c * T t i)) : ConwayRawSpace) = c • (0, (0, T)) := by
    simp only [Prod.smul_mk, smul_zero]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext t i
    rfl
  rw [h]
  exact griessConwayDecodeLinear.map_smul _ _

/-- The actual product A×Y carries the source pair character and row exchange. -/
theorem griessProd_ABC_zero_Y_exchange (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessProd (trialityABCBasis 0 p) (trialityXYZBasis 1 (finProdFinEquiv (d,j))) =
      trialityPairShortCharacter p d • trialityXYZExchange 1 p d j := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_ABC_zero_sparse,
    griessConwayEncode_Y_basis, trialityPairMatrix_raw_Y]
  simp only [qSign_boolean_add]
  change griessConwayDecode (0, (0, fun t i => trialityPairShortCharacter p d *
    ((if j = (griessCoordinatePair p).1 then
        trialityYTensor d (griessCoordinatePair p).2 t i else 0) +
      (if j = (griessCoordinatePair p).2 then
        trialityYTensor d (griessCoordinatePair p).1 t i else 0)))) = _
  rw [decode_tensor_smul]
  unfold trialityXYZExchange
  by_cases ha : j = (griessCoordinatePair p).1 <;>
    by_cases hb : j = (griessCoordinatePair p).2
  · exact False.elim ((griessCoordinatePair_ne p) (ha.symm.trans hb))
  · simp only [ha, griessCoordinatePair_ne p, ite_true, ite_false, add_zero]
    rw [← griessConwayEncode_Y_basis, griessConwayDecode_encode]
  · simp only [hb, (griessCoordinatePair_ne p).symm, ite_true, ite_false, zero_add]
    rw [← griessConwayEncode_Y_basis, griessConwayDecode_encode]
  · simp only [ha, hb, ite_false, add_zero]
    change trialityPairShortCharacter p d • griessConwayDecodeLinear 0 = _
    rw [map_zero, smul_zero]

/-- The actual product B×Z carries exactly the same source pair character and row exchange. -/
theorem griessProd_ABC_one_Z_exchange (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessProd (trialityABCBasis 1 p) (trialityXYZBasis 2 (finProdFinEquiv (d,j))) =
      trialityPairShortCharacter p d • trialityXYZExchange 2 p d j := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_B_sparse,
    griessConwayEncode_Z_basis, trialityPairB_raw_Z]
  simp only [qSign_boolean_add]
  change griessConwayDecode (0, (0, fun t i => trialityPairShortCharacter p d *
    ((if j = (griessCoordinatePair p).1 then
        trialityZTensor d (griessCoordinatePair p).2 t i else 0) +
      (if j = (griessCoordinatePair p).2 then
        trialityZTensor d (griessCoordinatePair p).1 t i else 0)))) = _
  rw [decode_tensor_smul]
  unfold trialityXYZExchange
  by_cases ha : j = (griessCoordinatePair p).1 <;>
    by_cases hb : j = (griessCoordinatePair p).2
  · exact False.elim ((griessCoordinatePair_ne p) (ha.symm.trans hb))
  · simp only [ha, griessCoordinatePair_ne p, ite_true, ite_false, add_zero]
    rw [← griessConwayEncode_Z_basis, griessConwayDecode_encode]
  · simp only [hb, (griessCoordinatePair_ne p).symm, ite_true, ite_false, zero_add]
    rw [← griessConwayEncode_Z_basis, griessConwayDecode_encode]
  · simp only [ha, hb, ite_false, add_zero]
    change trialityPairShortCharacter p d • griessConwayDecodeLinear 0 = _
    rw [map_zero, smul_zero]

/-- Triality carries every actual A×Y product to its actual B×Z product. -/
theorem triality_ABC_zero_Y_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis 0 p) (trialityXYZBasis 1 (finProdFinEquiv (d,j)))) =
      griessProd (sExtra (trialityABCBasis 0 p))
        (sExtra (trialityXYZBasis 1 (finProdFinEquiv (d,j)))) := by
  rw [griessProd_ABC_zero_Y_exchange, map_smul, trialityXYZExchange_cycle,
    sExtra_ABC_basis, sExtra_XYZ_basis]
  have h0 : trialityCycle 0 = 1 := by decide +kernel
  have h1 : trialityCycle 1 = 2 := by decide +kernel
  rw [h0, h1, griessProd_ABC_one_Z_exchange]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

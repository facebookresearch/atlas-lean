/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual C products on the even and odd spin-tensor source blocks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairYZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityABCProduct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- C is the sum of the two actual pair-short coordinates. -/
noncomputable def trialityPairCShort (p : Fin 276) : GriessShortIndex → ℝ :=
  Pi.single (Sum.inl (0,p)) 1 + Pi.single (Sum.inl (1,p)) 1

theorem griessConwayEncode_C_sparse (p : Fin 276) :
    griessConwayEncode (trialityABCBasis 2 p) = (0, (trialityPairCShort p, 0)) := by
  rw [griessConwayEncode_ABC_two_short]
  simp [conwayShortBasis, trialityPairCShort]

private theorem sparse_sum_sum {I : Type*} [Fintype I] [DecidableEq I]
    (r s : I) (F : I → ℝ) :
    (∑ i, (Pi.single r 1 + Pi.single s 1 : I → ℝ) i * F i) = F r + F s := by
  simp [Pi.add_apply, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]

/-- The exact signed pair-short tensor contraction before imposing any all-one parity. -/
theorem trialityPairC_raw_tensor (p : Fin 276) (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    (conwayRawProduct (0, (trialityPairCShort p, 0)) (0, (0, T))).2.2 t i =
      ((∑ j, spinOperator (griessShortQ (Sum.inl (0, p))) (fun v => T v j) t *
        conwayTensorCoefficient (Sum.inl (0, p)) j i) +
      (∑ j, spinOperator (griessShortQ (Sum.inl (1, p))) (fun v => T v j) t *
        conwayTensorCoefficient (Sum.inl (1, p)) j i)) / 8 := by
  dsimp only [conwayRawProduct]
  simp only [Pi.zero_apply, Matrix.zero_apply, zero_mul, mul_zero, add_zero,
    Finset.sum_const_zero, Matrix.trace_zero, zero_div, zero_add]
  have hterm (r : GriessShortIndex) :
      (∑ j, trialityPairCShort p r * spinOperator (griessShortQ r) (fun v => T v j) t *
        conwayTensorCoefficient r j i) =
      trialityPairCShort p r *
        (∑ j, spinOperator (griessShortQ r) (fun v => T v j) t *
          conwayTensorCoefficient r j i) := by
    simp_rw [mul_assoc]
    rw [Finset.mul_sum]
  simp_rw [hterm]
  rw [trialityPairCShort, sparse_sum_sum]

/-- On an all-one-even tensor, C uses the sum of the two pair coefficient matrices. -/
theorem trialityPairC_raw_tensor_even (p : Fin 276) (T : SpinIndex → Fin 24 → ℝ)
    (heven : ∀ t i, T (t + Pi.single 11 1) i = T t i) (t : SpinIndex) (i : Fin 24) :
    (conwayRawProduct (0, (trialityPairCShort p, 0)) (0, (0, T))).2.2 t i =
      qSign (golayEncoder t (griessCoordinatePair p).1 +
        golayEncoder t (griessCoordinatePair p).2) *
      (2 * T t i - 8 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if i = (griessCoordinatePair p).2 then 1 else 0)) * T t i) / 8 := by
  rw [trialityPairC_raw_tensor]
  simp_rw [spinOperator_griessPairMinus, spinOperator_griessPairPlus, heven]
  rw [← Finset.sum_add_distrib]
  have he (j : Fin 24) :
      qSign (golayEncoder t (griessCoordinatePair p).1 +
          golayEncoder t (griessCoordinatePair p).2) * T t j *
          conwayTensorCoefficient (Sum.inl (0, p)) j i +
        qSign (golayEncoder t (griessCoordinatePair p).1 +
          golayEncoder t (griessCoordinatePair p).2) * T t j *
          conwayTensorCoefficient (Sum.inl (1, p)) j i =
      qSign (golayEncoder t (griessCoordinatePair p).1 +
          golayEncoder t (griessCoordinatePair p).2) * T t j *
        (conwayTensorCoefficient (Sum.inl (0, p)) j i +
          conwayTensorCoefficient (Sum.inl (1, p)) j i) := by ring
  simp_rw [he, conwayTensorCoefficient_pair_sum]
  have hsum : (∑ j,
      qSign (golayEncoder t (griessCoordinatePair p).1 +
        golayEncoder t (griessCoordinatePair p).2) * T t j *
          (2 * (if j = i then 1 else 0) - 8 * trialityPairProjection p j i)) =
      qSign (golayEncoder t (griessCoordinatePair p).1 +
        golayEncoder t (griessCoordinatePair p).2) *
      (2 * T t i - 8 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if i = (griessCoordinatePair p).2 then 1 else 0)) * T t i) := by
    let c := qSign (golayEncoder t (griessCoordinatePair p).1 +
      golayEncoder t (griessCoordinatePair p).2)
    change (∑ j, c * T t j *
      (2 * (if j = i then 1 else 0) - 8 * trialityPairProjection p j i)) =
      c * (2 * T t i - 8 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if i = (griessCoordinatePair p).2 then 1 else 0)) * T t i)
    have hh (j : Fin 24) : c * T t j *
        (2 * (if j = i then 1 else 0) - 8 * trialityPairProjection p j i) =
        (2 * c) * (T t j * (if j = i then 1 else 0)) -
          (8 * c) * (trialityPairProjection p j i * T t j) := by ring
    simp_rw [hh]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      trialityPairProjection_tensor_apply]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  rw [hsum]

/-- On an all-one-odd tensor, C acts by the elementary spatial row exchange. -/
theorem trialityPairC_raw_tensor_odd (p : Fin 276) (T : SpinIndex → Fin 24 → ℝ)
    (hodd : ∀ t i, T (t + Pi.single 11 1) i = -T t i) (t : SpinIndex) (i : Fin 24) :
    (conwayRawProduct (0, (trialityPairCShort p, 0)) (0, (0, T))).2.2 t i =
      qSign (golayEncoder t (griessCoordinatePair p).1 +
        golayEncoder t (griessCoordinatePair p).2) *
      ((if i = (griessCoordinatePair p).1 then T t (griessCoordinatePair p).2 else 0) +
        (if i = (griessCoordinatePair p).2 then T t (griessCoordinatePair p).1 else 0)) := by
  rw [trialityPairC_raw_tensor]
  simp_rw [spinOperator_griessPairMinus, spinOperator_griessPairPlus, hodd]
  simp only [mul_neg, neg_mul]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
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

/-- C×Z has precisely the scalar obtained from the physical A×X multiplication. -/
theorem trialityPairC_raw_Z_tensor (p : Fin 276) (d : Fin 2048) (j : Fin 24)
    (t : SpinIndex) (i : Fin 24) :
    (conwayRawProduct (0, (trialityPairCShort p, 0)) (0, (0, trialityZTensor d j))).2.2 t i =
      trialityPairShortScalar p d j * trialityZTensor d j t i := by
  rw [trialityPairC_raw_tensor_even p _ (trialityZTensor_add_omega d j)]
  have hc := trialityZTensor_pair_character p d j t i
  rw [qSign_boolean_add] at hc
  change qSign (golayEncoder t (griessCoordinatePair p).1 +
    golayEncoder t (griessCoordinatePair p).2) * trialityZTensor d j t i =
    trialityPairShortCharacter p d * trialityZTensor d j t i at hc
  have he : qSign (golayEncoder t (griessCoordinatePair p).1 +
      golayEncoder t (griessCoordinatePair p).2) *
      (2 * trialityZTensor d j t i -
        8 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
          (if i = (griessCoordinatePair p).2 then 1 else 0)) * trialityZTensor d j t i) / 8 =
      (2 - 8 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if i = (griessCoordinatePair p).2 then 1 else 0))) / 8 *
        (qSign (golayEncoder t (griessCoordinatePair p).1 +
          golayEncoder t (griessCoordinatePair p).2) * trialityZTensor d j t i) := by ring
  rw [he, hc]
  by_cases hij : i = j
  · subst i
    have hn := griessCoordinatePair_ne p
    by_cases ha : j = (griessCoordinatePair p).1 <;>
      by_cases hb : j = (griessCoordinatePair p).2 <;>
      simp_all [trialityPairShortScalar] <;> ring
  · have hz : trialityZTensor d j t i = 0 := by simp [trialityZTensor, hij]
    simp only [hz, mul_zero]

/-- The complete raw C×Z product equals its actual scalar times Y. -/
theorem trialityPairC_raw_Z (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (0, (trialityPairCShort p, 0)) (0, (0, trialityZTensor d j)) =
      trialityPairShortScalar p d j • (0, (0, trialityZTensor d j)) := by
  apply Prod.ext
  · funext a b
    simp only [conwayRawProduct, Matrix.zero_apply, Pi.zero_apply, zero_mul, mul_zero,
      add_zero, ite_self, Finset.sum_const_zero, zero_div, Prod.smul_fst, smul_zero]
  · apply Prod.ext
    · funext r
      simp [conwayRawProduct, spinOperator, conwayShortPairing]
    · funext t i
      exact trialityPairC_raw_Z_tensor p d j t i

/-- The actual Griess product C×Z is the same derived scalar times Y. -/
theorem griessProd_ABC_two_Z_scalar (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessProd (trialityABCBasis 2 p) (trialityXYZBasis 2 (finProdFinEquiv (d, j))) =
      trialityPairShortScalar p d j • trialityXYZBasis 2 (finProdFinEquiv (d, j)) := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_C_sparse,
    griessConwayEncode_Z_basis, trialityPairC_raw_Z]
  have hs : griessConwayDecode
      (trialityPairShortScalar p d j • (0, (0, trialityZTensor d j))) =
      trialityPairShortScalar p d j • griessConwayDecode (0, (0, trialityZTensor d j)) :=
    griessConwayDecodeLinear.map_smul _ _
  rw [hs, ← griessConwayEncode_Z_basis, griessConwayDecode_encode]

/-- The complete raw C×Y product has exactly its source pair character and row exchange. -/
theorem trialityPairC_raw_Y (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (0, (trialityPairCShort p, 0)) (0, (0, trialityYTensor d j)) =
      (0, (0, fun t i =>
        (if j = (griessCoordinatePair p).1 then
            trialityYTensor d (griessCoordinatePair p).2 t i else 0) +
          (if j = (griessCoordinatePair p).2 then
            trialityYTensor d (griessCoordinatePair p).1 t i else 0))) := by
  apply Prod.ext
  · funext a b
    simp only [conwayRawProduct, Matrix.zero_apply, Pi.zero_apply, zero_mul, mul_zero,
      add_zero, ite_self, Finset.sum_const_zero, zero_div]
  · apply Prod.ext
    · funext r
      simp [conwayRawProduct, spinOperator, conwayShortPairing]
    · funext t i
      rw [trialityPairC_raw_tensor_odd p _ (trialityYTensor_add_omega d j)]
      rw [mul_add]
      simp only [mul_ite, mul_zero]
      rw [trialityYTensor_pair_character p d j t (griessCoordinatePair p).2,
        trialityYTensor_pair_character p d j t (griessCoordinatePair p).1]
      have h := congrArg (fun z : ℝ =>
        qSign (golayBooleanCast ((golayEncodedMask d.val).testBit
            (griessCoordinatePair p).1.val) +
          golayBooleanCast ((golayEncodedMask d.val).testBit
            (griessCoordinatePair p).2.val)) * z) (trialityYTensor_row_swap p d j t i)
      simpa only [mul_add, mul_ite, mul_zero, ← mul_assoc, qSign_sq, one_mul] using h

/-- The complete raw A×Z product carries the same pair character and source row exchange. -/
theorem trialityPairMatrix_raw_Z (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (trialityPairMatrix p, (0, 0)) (0, (0, trialityZTensor d j)) =
      (0, (0, fun t i =>
        (if j = (griessCoordinatePair p).1 then
            trialityZTensor d (griessCoordinatePair p).2 t i else 0) +
          (if j = (griessCoordinatePair p).2 then
            trialityZTensor d (griessCoordinatePair p).1 t i else 0))) := by
  rw [trialityPairMatrix_raw_restriction]
  refine Prod.ext rfl ?_
  apply Prod.ext
  · funext r
    simp only [Pi.zero_apply, mul_zero]
  · funext t i
    exact trialityZTensor_row_swap p d j t i

/-- The actual product C×Y exchanges source rows with no additional phase. -/
theorem griessProd_ABC_two_Y_exchange (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessProd (trialityABCBasis 2 p) (trialityXYZBasis 1 (finProdFinEquiv (d,j))) =
      trialityXYZExchange 1 p d j := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_C_sparse,
    griessConwayEncode_Y_basis, trialityPairC_raw_Y]
  unfold trialityXYZExchange
  by_cases ha : j = (griessCoordinatePair p).1 <;>
    by_cases hb : j = (griessCoordinatePair p).2
  · exact False.elim ((griessCoordinatePair_ne p) (ha.symm.trans hb))
  · simp only [ha, griessCoordinatePair_ne p, ite_true, ite_false, add_zero]
    rw [← griessConwayEncode_Y_basis, griessConwayDecode_encode]
  · simp only [hb, (griessCoordinatePair_ne p).symm, ite_true, ite_false, zero_add]
    rw [← griessConwayEncode_Y_basis, griessConwayDecode_encode]
  · simp only [ha, hb, ite_false, add_zero]
    exact griessConwayDecodeLinear.map_zero

/-- The actual product A×Z has the same source row exchange. -/
theorem griessProd_ABC_zero_Z_exchange (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessProd (trialityABCBasis 0 p) (trialityXYZBasis 2 (finProdFinEquiv (d,j))) =
      trialityXYZExchange 2 p d j := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_ABC_zero_sparse,
    griessConwayEncode_Z_basis, trialityPairMatrix_raw_Z]
  unfold trialityXYZExchange
  by_cases ha : j = (griessCoordinatePair p).1 <;>
    by_cases hb : j = (griessCoordinatePair p).2
  · exact False.elim ((griessCoordinatePair_ne p) (ha.symm.trans hb))
  · simp only [ha, griessCoordinatePair_ne p, ite_true, ite_false, add_zero]
    rw [← griessConwayEncode_Z_basis, griessConwayDecode_encode]
  · simp only [hb, (griessCoordinatePair_ne p).symm, ite_true, ite_false, zero_add]
    rw [← griessConwayEncode_Z_basis, griessConwayDecode_encode]
  · simp only [ha, hb, ite_false, add_zero]
    exact griessConwayDecodeLinear.map_zero

/-- Actual triality carries B×Y to C×Z. -/
theorem triality_ABC_one_Y_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis 1 p) (trialityXYZBasis 1 (finProdFinEquiv (d,j)))) =
      griessProd (sExtra (trialityABCBasis 1 p))
        (sExtra (trialityXYZBasis 1 (finProdFinEquiv (d,j)))) := by
  rw [griessProd_ABC_one_Y_scalar, map_smul, sExtra_ABC_basis, sExtra_XYZ_basis]
  have h1 : trialityCycle 1 = 2 := by decide +kernel
  rw [h1, griessProd_ABC_two_Z_scalar]

/-- Actual triality closes the scalar A×X, B×Y, C×Z cycle. -/
theorem triality_ABC_two_Z_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis 2 p) (trialityXYZBasis 2 (finProdFinEquiv (d,j)))) =
      griessProd (sExtra (trialityABCBasis 2 p))
        (sExtra (trialityXYZBasis 2 (finProdFinEquiv (d,j)))) := by
  rw [griessProd_ABC_two_Z_scalar, map_smul, sExtra_ABC_basis, sExtra_XYZ_basis]
  have h2 : trialityCycle 2 = 0 := by decide +kernel
  rw [h2, griessProd_ABC_zero_X_scalar]

/-- Actual triality carries C×Y to A×Z. -/
theorem triality_ABC_two_Y_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis 2 p) (trialityXYZBasis 1 (finProdFinEquiv (d,j)))) =
      griessProd (sExtra (trialityABCBasis 2 p))
        (sExtra (trialityXYZBasis 1 (finProdFinEquiv (d,j)))) := by
  rw [griessProd_ABC_two_Y_exchange, trialityXYZExchange_cycle,
    sExtra_ABC_basis, sExtra_XYZ_basis]
  have h1 : trialityCycle 1 = 2 := by decide +kernel
  have h2 : trialityCycle 2 = 0 := by decide +kernel
  rw [h1, h2, griessProd_ABC_zero_Z_exchange]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

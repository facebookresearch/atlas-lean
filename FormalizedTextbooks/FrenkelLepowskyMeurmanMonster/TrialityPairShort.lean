/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Pair-matrix multiplication on the X dictionary block and its triality image.
The scalar is derived from the actual norm-four physical short representative.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MatrixPairAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairMatrixRelations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual code sign at the two distinct spatial coordinates of a dictionary pair. -/
noncomputable def trialityPairShortCharacter (p : Fin 276) (d : Fin 2048) : ℝ :=
  (if (golayEncodedMask d.val).testBit (griessCoordinatePair p).1.val then -1 else 1) *
    (if (golayEncodedMask d.val).testBit (griessCoordinatePair p).2.val then -1 else 1)

/-- The exact A×X scalar, including the exceptional coordinate with value -3. -/
noncomputable def trialityPairShortScalar (p : Fin 276) (d : Fin 2048) (j : Fin 24) : ℝ :=
  trialityPairShortCharacter p d *
    (if j = (griessCoordinatePair p).1 ∨ j = (griessCoordinatePair p).2 then -3 else 1) / 4

/-- The physical X-label short vector in its normalized actual coordinates. -/
theorem griessShortVector_X_coordinate (d : Fin 2048) (j i : Fin 24) :
    griessShortVector (Sum.inr (Sum.inr (d, j))) i =
      (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
        (if i = j then -3 else 1) / Real.sqrt 8 := by
  unfold griessShortVector griessShortIntegral
  split_ifs <;> simp_all

private theorem normalized_short_product (x y : ℝ) :
    2 * (x / Real.sqrt 8) * (y / Real.sqrt 8) = x * y / 4 := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  calc
    _ = 2 * ((x / Real.sqrt 8) * (y / Real.sqrt 8)) := by ring
    _ = 2 * ((x * y) / (Real.sqrt 8 * Real.sqrt 8)) := by rw [div_mul_div_comm]
    _ = x * y / 4 := by rw [hs]; ring

private theorem exceptional_coordinate_product (a b j : Fin 24) (hab : a ≠ b) :
    (if a = j then (-3 : ℝ) else 1) * (if b = j then -3 else 1) =
      (if j = a ∨ j = b then -3 else 1) := by
  by_cases ha : j = a <;> by_cases hb : j = b <;> simp_all [eq_comm]

/-- The pair-short scalar is exactly twice the actual physical coordinate product. -/
theorem trialityPairShortScalar_eq_pairing (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    2 * griessShortVector (Sum.inr (Sum.inr (d, j))) (griessCoordinatePair p).1 *
      griessShortVector (Sum.inr (Sum.inr (d, j))) (griessCoordinatePair p).2 =
      trialityPairShortScalar p d j := by
  rw [griessShortVector_X_coordinate, griessShortVector_X_coordinate, normalized_short_product]
  unfold trialityPairShortScalar trialityPairShortCharacter
  have h := exceptional_coordinate_product (griessCoordinatePair p).1
    (griessCoordinatePair p).2 j (griessCoordinatePair_ne p)
  calc
    _ = ((if (golayEncodedMask d.val).testBit (griessCoordinatePair p).1.val then
          (-1 : ℝ) else 1) *
        (if (golayEncodedMask d.val).testBit (griessCoordinatePair p).2.val then -1 else 1)) *
      ((if (griessCoordinatePair p).1 = j then -3 else 1) *
        (if (griessCoordinatePair p).2 = j then -3 else 1)) / 4 := by ring
    _ = _ := by rw [h]

/-- A×X is a scalar multiple of the same actual X coordinate in the raw algebra. -/
theorem trialityPairMatrix_raw_X (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (trialityPairMatrix p, (0, 0))
      (0, ((Pi.single (Sum.inr (Sum.inr (d, j))) 1 : GriessShortIndex → ℝ), 0)) =
      trialityPairShortScalar p d j •
        (0, ((Pi.single (Sum.inr (Sum.inr (d, j))) 1 : GriessShortIndex → ℝ), 0)) := by
  rw [trialityPairMatrix_raw_restriction]
  apply Prod.ext
  · simp only [Prod.smul_fst, smul_zero]
  · apply Prod.ext
    · funext r
      simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      by_cases hr : r = Sum.inr (Sum.inr (d, j))
      · subst r
        rw [trialityPairShortScalar_eq_pairing]
      · simp only [Pi.single_eq_of_ne hr, mul_zero]
    · funext t i
      simp only [Pi.zero_apply, Prod.smul_snd, smul_zero]
      split_ifs <;> simp

/-- The B dictionary coordinate is the difference of the two actual pair-short lifts. -/
noncomputable def trialityPairBShort (p : Fin 276) : GriessShortIndex → ℝ :=
  Pi.single (Sum.inl (0, p)) 1 - Pi.single (Sum.inl (1, p)) 1

/-- The actual B coordinate has only its two indicated signed-short entries. -/
theorem griessConwayEncode_B_sparse (p : Fin 276) :
    griessConwayEncode (trialityABCBasis 1 p) = (0, (trialityPairBShort p, 0)) := by
  rw [griessConwayEncode_ABC_basis]
  apply Prod.ext
  · funext i j
    dsimp only
    split_ifs <;> simp
  · apply Prod.ext
    · funext r
      rcases r with ⟨u, q⟩ | (r | r)
      · fin_cases u <;> simp [trialityPairBShort, Pi.single_apply]
      · simp [trialityPairBShort]
      · simp [trialityPairBShort]
    · rfl

private theorem sparse_difference_sum {I : Type*} [Fintype I] [DecidableEq I]
    (r s : I) (F : I → ℝ) :
    (∑ i, (Pi.single r 1 - Pi.single s 1 : I → ℝ) i * F i) = F r - F s := by
  simp [Pi.sub_apply, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul]

/-- The exact signed pair-short tensor contraction before imposing any all-one parity. -/
theorem trialityPairB_raw_tensor (p : Fin 276) (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    (conwayRawProduct (0, (trialityPairBShort p, 0)) (0, (0, T))).2.2 t i =
      ((∑ j, spinOperator (griessShortQ (Sum.inl (0, p))) (fun v => T v j) t *
        conwayTensorCoefficient (Sum.inl (0, p)) j i) -
      (∑ j, spinOperator (griessShortQ (Sum.inl (1, p))) (fun v => T v j) t *
        conwayTensorCoefficient (Sum.inl (1, p)) j i)) / 8 := by
  dsimp only [conwayRawProduct]
  simp only [Pi.zero_apply, Matrix.zero_apply, zero_mul, mul_zero, add_zero,
    Finset.sum_const_zero, Matrix.trace_zero, zero_div, zero_add]
  have hterm (r : GriessShortIndex) :
      (∑ j, trialityPairBShort p r * spinOperator (griessShortQ r) (fun v => T v j) t *
        conwayTensorCoefficient r j i) =
      trialityPairBShort p r *
        (∑ j, spinOperator (griessShortQ r) (fun v => T v j) t *
          conwayTensorCoefficient r j i) := by
    simp_rw [mul_assoc]
    rw [Finset.mul_sum]
  simp_rw [hterm]
  rw [trialityPairBShort, sparse_difference_sum]

/-- On an all-one-odd tensor, B uses the sum of the two pair coefficient matrices. -/
theorem trialityPairB_raw_tensor_odd (p : Fin 276) (T : SpinIndex → Fin 24 → ℝ)
    (hodd : ∀ t i, T (t + Pi.single 11 1) i = -T t i) (t : SpinIndex) (i : Fin 24) :
    (conwayRawProduct (0, (trialityPairBShort p, 0)) (0, (0, T))).2.2 t i =
      qSign (golayEncoder t (griessCoordinatePair p).1 +
        golayEncoder t (griessCoordinatePair p).2) *
      (2 * T t i - 8 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if i = (griessCoordinatePair p).2 then 1 else 0)) * T t i) / 8 := by
  rw [trialityPairB_raw_tensor]
  simp_rw [spinOperator_griessPairMinus, spinOperator_griessPairPlus, hodd]
  rw [← Finset.sum_sub_distrib]
  have he (j : Fin 24) :
      qSign (golayEncoder t (griessCoordinatePair p).1 +
          golayEncoder t (griessCoordinatePair p).2) * T t j *
          conwayTensorCoefficient (Sum.inl (0, p)) j i -
        qSign (golayEncoder t (griessCoordinatePair p).1 +
          golayEncoder t (griessCoordinatePair p).2) * (-T t j) *
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

/-- B×Y has precisely the scalar obtained from the physical A×X multiplication. -/
theorem trialityPairB_raw_Y_tensor (p : Fin 276) (d : Fin 2048) (j : Fin 24)
    (t : SpinIndex) (i : Fin 24) :
    (conwayRawProduct (0, (trialityPairBShort p, 0)) (0, (0, trialityYTensor d j))).2.2 t i =
      trialityPairShortScalar p d j * trialityYTensor d j t i := by
  rw [trialityPairB_raw_tensor_odd p _ (trialityYTensor_add_omega d j)]
  have hc := trialityYTensor_pair_character p d j t i
  rw [qSign_boolean_add] at hc
  change qSign (golayEncoder t (griessCoordinatePair p).1 +
    golayEncoder t (griessCoordinatePair p).2) * trialityYTensor d j t i =
    trialityPairShortCharacter p d * trialityYTensor d j t i at hc
  have he : qSign (golayEncoder t (griessCoordinatePair p).1 +
      golayEncoder t (griessCoordinatePair p).2) *
      (2 * trialityYTensor d j t i -
        8 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
          (if i = (griessCoordinatePair p).2 then 1 else 0)) * trialityYTensor d j t i) / 8 =
      (2 - 8 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if i = (griessCoordinatePair p).2 then 1 else 0))) / 8 *
        (qSign (golayEncoder t (griessCoordinatePair p).1 +
          golayEncoder t (griessCoordinatePair p).2) * trialityYTensor d j t i) := by ring
  rw [he, hc]
  by_cases hij : i = j
  · subst i
    have hn := griessCoordinatePair_ne p
    by_cases ha : j = (griessCoordinatePair p).1 <;>
      by_cases hb : j = (griessCoordinatePair p).2 <;>
      simp_all [trialityPairShortScalar] <;> ring
  · have hz : trialityYTensor d j t i = 0 := by simp [trialityYTensor, hij]
    simp only [hz, mul_zero]

/-- The complete raw B×Y product equals its actual scalar times Y. -/
theorem trialityPairB_raw_Y (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (0, (trialityPairBShort p, 0)) (0, (0, trialityYTensor d j)) =
      trialityPairShortScalar p d j • (0, (0, trialityYTensor d j)) := by
  apply Prod.ext
  · funext a b
    simp only [conwayRawProduct, Matrix.zero_apply, Pi.zero_apply, zero_mul, mul_zero,
      add_zero, ite_self, Finset.sum_const_zero, zero_div, Prod.smul_fst, smul_zero]
  · apply Prod.ext
    · funext r
      simp [conwayRawProduct, spinOperator, conwayShortPairing]
    · funext t i
      exact trialityPairB_raw_Y_tensor p d j t i

/-- The exact actual Griess product A×X is the derived physical scalar times X. -/
theorem griessProd_ABC_zero_X_scalar (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessProd (trialityABCBasis 0 p) (trialityXYZBasis 0 (finProdFinEquiv (d, j))) =
      trialityPairShortScalar p d j • trialityXYZBasis 0 (finProdFinEquiv (d, j)) := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_ABC_zero_sparse,
    griessConwayEncode_X_basis, trialityPairMatrix_raw_X]
  have hs : griessConwayDecode (trialityPairShortScalar p d j •
      (0, ((Pi.single (Sum.inr (Sum.inr (d, j))) 1 : GriessShortIndex → ℝ), 0))) =
      trialityPairShortScalar p d j • griessConwayDecode
        (0, ((Pi.single (Sum.inr (Sum.inr (d, j))) 1 : GriessShortIndex → ℝ), 0)) :=
    griessConwayDecodeLinear.map_smul _ _
  rw [hs, ← griessConwayEncode_X_basis, griessConwayDecode_encode]

/-- The actual Griess product B×Y is the same derived scalar times Y. -/
theorem griessProd_ABC_one_Y_scalar (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessProd (trialityABCBasis 1 p) (trialityXYZBasis 1 (finProdFinEquiv (d, j))) =
      trialityPairShortScalar p d j • trialityXYZBasis 1 (finProdFinEquiv (d, j)) := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_B_sparse,
    griessConwayEncode_Y_basis, trialityPairB_raw_Y]
  have hs : griessConwayDecode
      (trialityPairShortScalar p d j • (0, (0, trialityYTensor d j))) =
      trialityPairShortScalar p d j • griessConwayDecode (0, (0, trialityYTensor d j)) :=
    griessConwayDecodeLinear.map_smul _ _
  rw [hs, ← griessConwayEncode_Y_basis, griessConwayDecode_encode]

/-- Actual triality carries A×X to B×Y for every pair, code label, and coordinate. -/
theorem triality_ABC_zero_X_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis 0 p) (trialityXYZBasis 0 (finProdFinEquiv (d, j)))) =
      griessProd (sExtra (trialityABCBasis 0 p))
        (sExtra (trialityXYZBasis 0 (finProdFinEquiv (d, j)))) := by
  have hc : trialityCycle 0 = 1 := by decide +kernel
  simp only [griessProd_ABC_zero_X_scalar, map_smul, sExtra_ABC_basis,
    sExtra_XYZ_basis, hc, griessProd_ABC_one_Y_scalar]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

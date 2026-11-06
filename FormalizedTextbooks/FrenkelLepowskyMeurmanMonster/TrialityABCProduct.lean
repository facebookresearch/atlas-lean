/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Multiplication of the A, B and C dictionary vectors belonging to one coordinate pair.
The three squares are the same diagonal vector, and each mixed product is
minus four times the remaining vector. The actual triality cycles this table.
Source: Conway, Invent. Math. 79 (1985), §12, DOI: 10.1007/BF01388521;
Seysen, arXiv:2002.10921v3, §8.1 and Table 5.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MatrixPairAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCommutativity
@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
theorem griessConwayEncode_ABC_one_short (p : Fin 276) :
    griessConwayEncode (trialityABCBasis 1 p) =
      conwayShortBasis (Sum.inl (0, p)) - conwayShortBasis (Sum.inl (1, p)) := by
  rw [griessConwayEncode_ABC_basis]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · funext i j
    split_ifs <;> simp [conwayShortBasis]
  · funext r
    rcases r with ⟨s, q⟩ | (r | r)
    · rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
        simp [conwayShortBasis, Pi.single_apply]
    · simp [conwayShortBasis]
    · simp [conwayShortBasis]
  · simp [conwayShortBasis]

set_option backward.isDefEq.respectTransparency false in
theorem griessConwayEncode_ABC_two_short (p : Fin 276) :
    griessConwayEncode (trialityABCBasis 2 p) =
      conwayShortBasis (Sum.inl (0, p)) + conwayShortBasis (Sum.inl (1, p)) := by
  rw [griessConwayEncode_ABC_basis]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · funext i j
    split_ifs <;> simp [conwayShortBasis]
  · funext r
    rcases r with ⟨s, q⟩ | (r | r)
    · rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
        simp [conwayShortBasis, Pi.single_apply]
    · simp [conwayShortBasis]
    · simp [conwayShortBasis]
  · simp [conwayShortBasis]

theorem conwayRawProduct_sub_left (x y z : ConwayRawSpace) :
    conwayRawProduct (x - y) z = conwayRawProduct x z - conwayRawProduct y z := by
  change conwayRawProductLinear (x - y) z = _
  rw [map_sub, LinearMap.sub_apply]
  rfl

theorem conwayRawProduct_sub_right (x y z : ConwayRawSpace) :
    conwayRawProduct x (y - z) = conwayRawProduct x y - conwayRawProduct x z := by
  change conwayRawProductLinear x (y - z) = _
  rw [map_sub]
  rfl

theorem conwayRawProduct_pairMinusPlus (p : Fin 276) :
    conwayRawProduct (conwayShortBasis (Sum.inl (0, p)))
      (conwayShortBasis (Sum.inl (1, p))) = 0 := by
  have hp : leechIntegralPairing (griessShortIntegral (Sum.inl (0, p)))
      (griessShortIntegral (Sum.inl (1, p))) ≠ 16 := by
    rw [griessPairMinusPlus_pairing]
    norm_num
  have hm : leechIntegralPairing (griessShortIntegral (Sum.inl (0, p)))
      (griessShortIntegral (Sum.inl (1, p))) ≠ -16 := by
    rw [griessPairMinusPlus_pairing]
    norm_num
  have hzero : ((fun _ _ : Fin 24 => (0 : ℝ)), (0, 0)) = (0 : ConwayRawSpace) := by
    rfl
  simpa only [Sum.inl.injEq, Prod.mk.injEq, show (0 : Fin 2) ≠ 1 by decide,
    show (1 : Fin 2) ≠ 0 by decide, false_and, and_false, ite_false, hzero] using
    conwayRawProduct_shortBasis_of_pairing (Sum.inl (0, p)) (Sum.inl (1, p)) hp hm

theorem conwayRawProduct_pairPlusMinus (p : Fin 276) :
    conwayRawProduct (conwayShortBasis (Sum.inl (1, p)))
      (conwayShortBasis (Sum.inl (0, p))) = 0 := by
  have hc : leechIntegralPairing (griessShortIntegral (Sum.inl (1, p)))
      (griessShortIntegral (Sum.inl (0, p))) = 0 := by
    simpa only [leechIntegralPairing, mul_comm] using griessPairMinusPlus_pairing p
  have hp : leechIntegralPairing (griessShortIntegral (Sum.inl (1, p)))
      (griessShortIntegral (Sum.inl (0, p))) ≠ 16 := by rw [hc]; norm_num
  have hm : leechIntegralPairing (griessShortIntegral (Sum.inl (1, p)))
      (griessShortIntegral (Sum.inl (0, p))) ≠ -16 := by rw [hc]; norm_num
  have hzero : ((fun _ _ : Fin 24 => (0 : ℝ)), (0, 0)) = (0 : ConwayRawSpace) := by
    rfl
  simpa only [Sum.inl.injEq, Prod.mk.injEq, show (0 : Fin 2) ≠ 1 by decide,
    show (1 : Fin 2) ≠ 0 by decide, false_and, and_false, ite_false, hzero] using
    conwayRawProduct_shortBasis_of_pairing (Sum.inl (1, p)) (Sum.inl (0, p)) hp hm

theorem griessPairOuter_sum (p : Fin 276) (i j : Fin 24) :
    griessShortVector (Sum.inl (0, p)) i * griessShortVector (Sum.inl (0, p)) j +
      griessShortVector (Sum.inl (1, p)) i * griessShortVector (Sum.inl (1, p)) j =
      4 * ((Matrix.vecMulVec (Pi.single (griessCoordinatePair p).1 1)
        (Pi.single (griessCoordinatePair p).1 1) +
        Matrix.vecMulVec (Pi.single (griessCoordinatePair p).2 1)
          (Pi.single (griessCoordinatePair p).2 1)) : Matrix (Fin 24) (Fin 24) ℝ) i j := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  simp only [griessShortVector, div_mul_div_comm, hs]
  simp only [griessShortIntegral, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply]
  split_ifs <;> norm_num at *

theorem griessPairOuter_sub (p : Fin 276) (i j : Fin 24) :
    griessShortVector (Sum.inl (0, p)) i * griessShortVector (Sum.inl (0, p)) j -
      griessShortVector (Sum.inl (1, p)) i * griessShortVector (Sum.inl (1, p)) j =
      -4 * trialityPairMatrix p i j := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  simp only [griessShortVector, div_mul_div_comm, hs]
  simp only [griessShortIntegral, trialityPairMatrix, Matrix.add_apply,
    Matrix.vecMulVec_apply, Pi.single_apply]
  split_ifs <;> norm_num at *

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_ABC_one_square (p : Fin 276) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 1 p))
      (griessConwayEncode (trialityABCBasis 1 p)) =
      ((4 : ℝ) • (trialityPairMatrix p * trialityPairMatrix p), (0, 0)) := by
  rw [griessConwayEncode_ABC_one_short, conwayRawProduct_sub_left,
    conwayRawProduct_sub_right, conwayRawProduct_sub_right,
    conwayRawProduct_shortBasis_square, conwayRawProduct_shortBasis_square,
    conwayRawProduct_pairMinusPlus, conwayRawProduct_pairPlusMinus]
  simp only [sub_zero, zero_sub, sub_neg_eq_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i j
    change griessShortVector (Sum.inl (0, p)) i * griessShortVector (Sum.inl (0, p)) j +
      griessShortVector (Sum.inl (1, p)) i * griessShortVector (Sum.inl (1, p)) j = _
    rw [griessPairOuter_sum, trialityPairMatrix_square]
    rfl
  · simp
  · simp

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_ABC_two_square (p : Fin 276) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 2 p))
      (griessConwayEncode (trialityABCBasis 2 p)) =
      ((4 : ℝ) • (trialityPairMatrix p * trialityPairMatrix p), (0, 0)) := by
  rw [griessConwayEncode_ABC_two_short, conwayRawProduct_add_left,
    conwayRawProduct_add_right, conwayRawProduct_add_right,
    conwayRawProduct_shortBasis_square, conwayRawProduct_shortBasis_square,
    conwayRawProduct_pairMinusPlus, conwayRawProduct_pairPlusMinus]
  simp only [add_zero, zero_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i j
    change griessShortVector (Sum.inl (0, p)) i * griessShortVector (Sum.inl (0, p)) j +
      griessShortVector (Sum.inl (1, p)) i * griessShortVector (Sum.inl (1, p)) j = _
    rw [griessPairOuter_sum, trialityPairMatrix_square]
    rfl
  · simp
  · simp

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_ABC_one_two (p : Fin 276) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 1 p))
      (griessConwayEncode (trialityABCBasis 2 p)) =
      ((-4 : ℝ) • trialityPairMatrix p, (0, 0)) := by
  rw [griessConwayEncode_ABC_one_short, griessConwayEncode_ABC_two_short,
    conwayRawProduct_sub_left, conwayRawProduct_add_right, conwayRawProduct_add_right,
    conwayRawProduct_shortBasis_square, conwayRawProduct_shortBasis_square,
    conwayRawProduct_pairMinusPlus, conwayRawProduct_pairPlusMinus]
  simp only [add_zero, zero_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i j
    change griessShortVector (Sum.inl (0, p)) i * griessShortVector (Sum.inl (0, p)) j -
      griessShortVector (Sum.inl (1, p)) i * griessShortVector (Sum.inl (1, p)) j = _
    rw [griessPairOuter_sub]
    rfl
  · simp
  · simp

theorem griessPair_same_short_pairing (p : Fin 276) (s : Fin 2) :
    2 * griessShortVector (Sum.inl (s, p)) (griessCoordinatePair p).1 *
      griessShortVector (Sum.inl (s, p)) (griessCoordinatePair p).2 =
      if s = 0 then -4 else 4 := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hn := griessCoordinatePair_ne p
  simp only [griessShortVector, mul_assoc, div_mul_div_comm, hs]
  by_cases h : s = 0 <;> norm_num [griessShortIntegral, h, hn, hn.symm]

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_ABC_zero_one (p : Fin 276) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 0 p))
      (griessConwayEncode (trialityABCBasis 1 p)) =
      (-4 : ℝ) • griessConwayEncode (trialityABCBasis 2 p) := by
  rw [griessConwayEncode_ABC_zero_sparse, griessConwayEncode_ABC_one_short,
    griessConwayEncode_ABC_two_short]
  simp only [conwayShortBasis, Prod.mk_sub_mk, sub_self, Prod.mk_add_mk, add_zero]
  rw [trialityPairMatrix_raw_restriction]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · simp
  · funext r
    by_cases h0 : r = Sum.inl (0, p)
    · subst r
      rw [griessPair_same_short_pairing]
      simp
    · by_cases h1 : r = Sum.inl (1, p)
      · subst r
        rw [griessPair_same_short_pairing]
        simp
      · simp [h0, h1]
  · funext t i
    simp

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_ABC_zero_two (p : Fin 276) :
    conwayRawProduct (griessConwayEncode (trialityABCBasis 0 p))
      (griessConwayEncode (trialityABCBasis 2 p)) =
      (-4 : ℝ) • griessConwayEncode (trialityABCBasis 1 p) := by
  rw [griessConwayEncode_ABC_zero_sparse, griessConwayEncode_ABC_two_short,
    griessConwayEncode_ABC_one_short]
  simp only [conwayShortBasis, Prod.mk_sub_mk, sub_self, Prod.mk_add_mk, add_zero]
  rw [trialityPairMatrix_raw_restriction]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals dsimp only
  · simp
  · funext r
    by_cases h0 : r = Sum.inl (0, p)
    · subst r
      rw [griessPair_same_short_pairing]
      simp
    · by_cases h1 : r = Sum.inl (1, p)
      · subst r
        rw [griessPair_same_short_pairing]
        simp
      · simp [h0, h1]
  · funext t i
    simp

theorem trialityPairMatrix_square_diagonal (p : Fin 276) :
    trialityPairMatrix p * trialityPairMatrix p =
      Matrix.diagonal ((Pi.single (griessCoordinatePair p).1 1 : Fin 24 → ℝ) +
        Pi.single (griessCoordinatePair p).2 1) := by
  rw [trialityPairMatrix_square]
  ext i j
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.diagonal_apply,
    Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp_all

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_zero_square (p : Fin 276) :
    griessProd (trialityABCBasis 0 p) (trialityABCBasis 0 p) =
      trialityDiagonalVector ((4 : ℝ) •
        ((Pi.single (griessCoordinatePair p).1 1 : Fin 24 → ℝ) +
          Pi.single (griessCoordinatePair p).2 1)) := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_ABC_zero_sparse,
    trialityPairMatrix_raw_square, trialityPairMatrix_square_diagonal]
  have hm (d : Fin 24 → ℝ) : (4 : ℝ) • Matrix.diagonal d = Matrix.diagonal ((4 : ℝ) • d) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hm, ← griessConwayEncode_diagonal, griessConwayDecode_encode]

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_one_square (p : Fin 276) :
    griessProd (trialityABCBasis 1 p) (trialityABCBasis 1 p) =
      griessProd (trialityABCBasis 0 p) (trialityABCBasis 0 p) := by
  rw [griessProd_eq_conwayRawProduct, griessProd_eq_conwayRawProduct,
    griessConwayEncode_ABC_zero_sparse, trialityPairMatrix_raw_square,
    conwayRawProduct_ABC_one_square]

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_two_square (p : Fin 276) :
    griessProd (trialityABCBasis 2 p) (trialityABCBasis 2 p) =
      griessProd (trialityABCBasis 0 p) (trialityABCBasis 0 p) := by
  rw [griessProd_eq_conwayRawProduct, griessProd_eq_conwayRawProduct,
    griessConwayEncode_ABC_zero_sparse, trialityPairMatrix_raw_square,
    conwayRawProduct_ABC_two_square]

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_zero_one (p : Fin 276) :
    griessProd (trialityABCBasis 0 p) (trialityABCBasis 1 p) = (-4 : ℝ) • trialityABCBasis 2 p := by
  rw [griessProd_eq_conwayRawProduct, conwayRawProduct_ABC_zero_one]
  change griessConwayDecodeLinear ((-4 : ℝ) • griessConwayEncode (trialityABCBasis 2 p)) = _
  rw [map_smul]
  exact congrArg (fun x : GriessSpace => (-4 : ℝ) • x) (griessConwayDecode_encode _)

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_zero_two (p : Fin 276) :
    griessProd (trialityABCBasis 0 p) (trialityABCBasis 2 p) = (-4 : ℝ) • trialityABCBasis 1 p := by
  rw [griessProd_eq_conwayRawProduct, conwayRawProduct_ABC_zero_two]
  change griessConwayDecodeLinear ((-4 : ℝ) • griessConwayEncode (trialityABCBasis 1 p)) = _
  rw [map_smul]
  exact congrArg (fun x : GriessSpace => (-4 : ℝ) • x) (griessConwayDecode_encode _)

set_option backward.isDefEq.respectTransparency false in
theorem griessProd_ABC_one_two (p : Fin 276) :
    griessProd (trialityABCBasis 1 p) (trialityABCBasis 2 p) = (-4 : ℝ) • trialityABCBasis 0 p := by
  rw [griessProd_eq_conwayRawProduct, conwayRawProduct_ABC_one_two]
  have he : ((-4 : ℝ) • trialityPairMatrix p, (0, 0)) =
      (-4 : ℝ) • griessConwayEncode (trialityABCBasis 0 p) := by
    rw [griessConwayEncode_ABC_zero_sparse]
    refine Prod.ext rfl ?_
    simp
  rw [he]
  change griessConwayDecodeLinear ((-4 : ℝ) • griessConwayEncode (trialityABCBasis 0 p)) = _
  rw [map_smul]
  exact congrArg (fun x : GriessSpace => (-4 : ℝ) • x) (griessConwayDecode_encode _)

theorem griessProd_ABC_one_zero (p : Fin 276) :
    griessProd (trialityABCBasis 1 p) (trialityABCBasis 0 p) = (-4 : ℝ) • trialityABCBasis 2 p := by
  rw [griessProd_comm, griessProd_ABC_zero_one]

theorem griessProd_ABC_two_zero (p : Fin 276) :
    griessProd (trialityABCBasis 2 p) (trialityABCBasis 0 p) = (-4 : ℝ) • trialityABCBasis 1 p := by
  rw [griessProd_comm, griessProd_ABC_zero_two]

theorem griessProd_ABC_two_one (p : Fin 276) :
    griessProd (trialityABCBasis 2 p) (trialityABCBasis 1 p) = (-4 : ℝ) • trialityABCBasis 0 p := by
  rw [griessProd_comm, griessProd_ABC_one_two]

theorem sExtra_preserves_ABC_same_pair (p : Fin 276) (s t : Fin 3) :
    sExtra (griessProd (trialityABCBasis s p) (trialityABCBasis t p)) =
      griessProd (sExtra (trialityABCBasis s p)) (sExtra (trialityABCBasis t p)) := by
  have h0 : trialityCycle (0 : Fin 3) = 1 := by decide +kernel
  have h1 : trialityCycle (1 : Fin 3) = 2 := by decide +kernel
  have h2 : trialityCycle (2 : Fin 3) = 0 := by decide +kernel
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
  all_goals simp only [sExtra_ABC_basis, h0, h1, h2, griessProd_ABC_one_square,
    griessProd_ABC_two_square, griessProd_ABC_zero_square, griessProd_ABC_zero_one,
    griessProd_ABC_zero_two, griessProd_ABC_one_two, griessProd_ABC_one_zero,
    griessProd_ABC_two_zero, griessProd_ABC_two_one, map_smul, sExtra_diagonal]
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

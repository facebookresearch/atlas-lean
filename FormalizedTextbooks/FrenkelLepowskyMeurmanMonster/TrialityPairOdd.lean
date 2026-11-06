/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact pair-short products with odd-coordinate source basis vectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairOddQProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairCZ

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

noncomputable def conwayPairOddExchange (p : Fin 276) (d : Fin 2048)
    (j : Fin 24) : ConwayRawSpace :=
  (if j = (griessCoordinatePair p).1 then
    conwayShortBasis (Sum.inr (Sum.inr (d, (griessCoordinatePair p).2))) else 0) +
  (if j = (griessCoordinatePair p).2 then
    conwayShortBasis (Sum.inr (Sum.inr (d, (griessCoordinatePair p).1))) else 0)

theorem conwayShortBasis_pairOdd_selector (s : Fin 2) (p : Fin 276)
    (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (conwayShortBasis (Sum.inl (s,p)))
      (conwayShortBasis (Sum.inr (Sum.inr (d,j)))) =
      if s = griessPairOddColor p d then
        (if s = 0 then (1 : ℝ) else -1) • conwayPairOddExchange p d j else 0 := by
  by_cases hs : s = griessPairOddColor p d
  · subst s
    rw [ite_eq_left rfl]
    by_cases ha : j = (griessCoordinatePair p).1
    · subst j
      rw [conwayShortBasis_pairOdd_left]
      simp [conwayPairOddExchange, griessCoordinatePair_ne p]
    · by_cases hb : j = (griessCoordinatePair p).2
      · subst j
        rw [conwayShortBasis_pairOdd_right]
        simp [conwayPairOddExchange, (griessCoordinatePair_ne p).symm]
      · rw [conwayShortBasis_pairOdd_zero _ _ _ _ (Or.inr ⟨ha,hb⟩)]
        simp [conwayPairOddExchange, ha, hb]
  · rw [ite_eq_right hs, conwayShortBasis_pairOdd_zero _ _ _ _ (Or.inl hs)]

theorem griessConwayEncode_exchange_X (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessConwayEncode (trialityXYZExchange 0 p d j) = conwayPairOddExchange p d j := by
  unfold trialityXYZExchange conwayPairOddExchange
  by_cases ha : j = (griessCoordinatePair p).1 <;>
    by_cases hb : j = (griessCoordinatePair p).2
  · exact False.elim ((griessCoordinatePair_ne p) (ha.symm.trans hb))
  · simp only [ha, griessCoordinatePair_ne p, ite_true, ite_false, add_zero]
    exact griessConwayEncode_X_basis d (griessCoordinatePair p).2
  · simp only [hb, (griessCoordinatePair_ne p).symm, ite_true, ite_false, zero_add]
    exact griessConwayEncode_X_basis d (griessCoordinatePair p).1
  · simp only [ha, hb, ite_false, add_zero]
    exact griessConwayEncodeLinear.map_zero

theorem conwayPairOdd_B_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (conwayShortBasis (Sum.inl (0,p)) -
      conwayShortBasis (Sum.inl (1,p)))
      (conwayShortBasis (Sum.inr (Sum.inr (d,j)))) = conwayPairOddExchange p d j := by
  rw [conwayRawProduct_sub_left, conwayShortBasis_pairOdd_selector,
    conwayShortBasis_pairOdd_selector]
  have hc := (griessPairOddColor p d).isLt
  by_cases h : griessPairOddColor p d = 0
  · simp [h]
  · have h1 : griessPairOddColor p d = 1 := by apply Fin.ext; simp at h ⊢; omega
    simp [h1]

theorem conwayPairOdd_C_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    conwayRawProduct (conwayShortBasis (Sum.inl (0,p)) +
      conwayShortBasis (Sum.inl (1,p)))
      (conwayShortBasis (Sum.inr (Sum.inr (d,j)))) =
      (if griessPairOddColor p d = 0 then (1 : ℝ) else -1) •
        conwayPairOddExchange p d j := by
  rw [conwayRawProduct_add_left, conwayShortBasis_pairOdd_selector,
    conwayShortBasis_pairOdd_selector]
  have hc := (griessPairOddColor p d).isLt
  by_cases h : griessPairOddColor p d = 0
  · simp [h]
  · have h1 : griessPairOddColor p d = 1 := by apply Fin.ext; simp at h ⊢; omega
    simp [h1]

theorem griessPairOddColor_character (p : Fin 276) (d : Fin 2048) :
    (if griessPairOddColor p d = 0 then (1 : ℝ) else -1) =
      trialityPairShortCharacter p d := by
  unfold griessPairOddColor trialityPairShortCharacter
  cases ha : (golayEncodedMask d.val).testBit (griessCoordinatePair p).1.val <;>
    cases hb : (golayEncodedMask d.val).testBit (griessCoordinatePair p).2.val <;>
      simp

theorem griessProd_ABC_one_X_exchange (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessProd (trialityABCBasis 1 p) (trialityXYZBasis 0 (finProdFinEquiv (d,j))) =
      trialityXYZExchange 0 p d j := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_ABC_one_short,
    griessConwayEncode_X_basis]
  change griessConwayDecode (conwayRawProduct
    (conwayShortBasis (Sum.inl (0,p)) - conwayShortBasis (Sum.inl (1,p)))
    (conwayShortBasis (Sum.inr (Sum.inr (d,j))))) = _
  rw [conwayPairOdd_B_product, ← griessConwayEncode_exchange_X, griessConwayDecode_encode]

theorem griessProd_ABC_two_X_exchange (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    griessProd (trialityABCBasis 2 p) (trialityXYZBasis 0 (finProdFinEquiv (d,j))) =
      trialityPairShortCharacter p d • trialityXYZExchange 0 p d j := by
  rw [griessProd_eq_conwayRawProduct, griessConwayEncode_ABC_two_short,
    griessConwayEncode_X_basis]
  change griessConwayDecode (conwayRawProduct
    (conwayShortBasis (Sum.inl (0,p)) + conwayShortBasis (Sum.inl (1,p)))
    (conwayShortBasis (Sum.inr (Sum.inr (d,j))))) = _
  rw [conwayPairOdd_C_product, griessPairOddColor_character,
    ← griessConwayEncode_exchange_X]
  change griessConwayDecodeLinear (_ • _) = _
  rw [map_smul]
  change _ • griessConwayDecode (griessConwayEncode _) = _
  rw [griessConwayDecode_encode]

/-- Triality carries A×Z to B×X with the exact unsigned endpoint exchange. -/
theorem triality_ABC_zero_Z_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis 0 p) (trialityXYZBasis 2 (finProdFinEquiv (d,j)))) =
      griessProd (sExtra (trialityABCBasis 0 p))
        (sExtra (trialityXYZBasis 2 (finProdFinEquiv (d,j)))) := by
  rw [griessProd_ABC_zero_Z_exchange, trialityXYZExchange_cycle,
    sExtra_ABC_basis, sExtra_XYZ_basis]
  have h0 : trialityCycle 0 = 1 := by decide +kernel
  have h2 : trialityCycle 2 = 0 := by decide +kernel
  rw [h0, h2, griessProd_ABC_one_X_exchange]

/-- Triality carries B×X to C×Y with the same unsigned endpoint exchange. -/
theorem triality_ABC_one_X_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis 1 p) (trialityXYZBasis 0 (finProdFinEquiv (d,j)))) =
      griessProd (sExtra (trialityABCBasis 1 p))
        (sExtra (trialityXYZBasis 0 (finProdFinEquiv (d,j)))) := by
  rw [griessProd_ABC_one_X_exchange, trialityXYZExchange_cycle,
    sExtra_ABC_basis, sExtra_XYZ_basis]
  have h0 : trialityCycle 0 = 1 := by decide +kernel
  have h1 : trialityCycle 1 = 2 := by decide +kernel
  rw [h0, h1, griessProd_ABC_two_Y_exchange]

/-- Triality carries B×Z to C×X, preserving the actual Golay pair character. -/
theorem triality_ABC_one_Z_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis 1 p) (trialityXYZBasis 2 (finProdFinEquiv (d,j)))) =
      griessProd (sExtra (trialityABCBasis 1 p))
        (sExtra (trialityXYZBasis 2 (finProdFinEquiv (d,j)))) := by
  rw [griessProd_ABC_one_Z_exchange, map_smul, trialityXYZExchange_cycle,
    sExtra_ABC_basis, sExtra_XYZ_basis]
  have h1 : trialityCycle 1 = 2 := by decide +kernel
  have h2 : trialityCycle 2 = 0 := by decide +kernel
  rw [h1, h2, griessProd_ABC_two_X_exchange]

/-- Triality carries C×X to A×Y, preserving the same actual character. -/
theorem triality_ABC_two_X_product (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis 2 p) (trialityXYZBasis 0 (finProdFinEquiv (d,j)))) =
      griessProd (sExtra (trialityABCBasis 2 p))
        (sExtra (trialityXYZBasis 0 (finProdFinEquiv (d,j)))) := by
  rw [griessProd_ABC_two_X_exchange, map_smul, trialityXYZExchange_cycle,
    sExtra_ABC_basis, sExtra_XYZ_basis]
  have h0 : trialityCycle 0 = 1 := by decide +kernel
  have h2 : trialityCycle 2 = 0 := by decide +kernel
  rw [h0, h2, griessProd_ABC_zero_Y_exchange]

/-- All nine ABC×XYZ source-basis products satisfy actual triality covariance. -/
theorem triality_ABC_XYZ_product (s t : Fin 3) (p : Fin 276)
    (d : Fin 2048) (j : Fin 24) :
    sExtra (griessProd (trialityABCBasis s p) (trialityXYZBasis t (finProdFinEquiv (d,j)))) =
      griessProd (sExtra (trialityABCBasis s p))
        (sExtra (trialityXYZBasis t (finProdFinEquiv (d,j)))) := by
  fin_cases s <;> fin_cases t
  · exact triality_ABC_zero_X_product p d j
  · exact triality_ABC_zero_Y_product p d j
  · exact triality_ABC_zero_Z_product p d j
  · exact triality_ABC_one_X_product p d j
  · exact triality_ABC_one_Y_product p d j
  · exact triality_ABC_one_Z_product p d j
  · exact triality_ABC_two_X_product p d j
  · exact triality_ABC_two_Y_product p d j
  · exact triality_ABC_two_Z_product p d j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

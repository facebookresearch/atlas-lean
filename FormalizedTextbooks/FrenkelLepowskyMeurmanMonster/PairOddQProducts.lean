/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Exact preferred-Q products between the pair and odd short-vector families.
The output label and central phase are computed from the proved source
spin coordinates, with no assumption about Conway multiplication.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairQProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairEdgeQProducts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem sourceTheta_omega_zero : ∀ i : Fin 12, sourceCodeTheta i 11 = 0 := by
  decide +kernel

private theorem sourceAssociator_omega_zero : ∀ i j : Fin 12,
    golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit (11 : Fin 12).val) = 0 := by
  decide +kernel

/-- The source theta adjustment of a lower code label has zero all-one coordinate. -/
theorem sourceWordTheta_low_omega : ∀ d : Fin 2048,
    sourceWordTheta ⟨d.val, by omega⟩ 11 = 0 := by
  intro d
  change golayBooleanCast ((parkerThetaMask d.val).testBit 11) = 0
  have hm := sourceCodeThetaPolynomial_mask ⟨d.val, by omega⟩ (11 : Fin 12)
  have hz : sourceCodeThetaPolynomial
      (golayLabelCoefficients ⟨d.val, by omega⟩) 11 = 0 := by
    simp only [sourceCodeThetaPolynomial, sourceTheta_omega_zero, sourceAssociator_omega_zero,
      mul_zero, ite_self, Finset.sum_const_zero, add_zero]
  exact hm.trans hz

/-- The odd-family preferred lift has modulation one at the all-one generator. -/
theorem griessOdd_modulation_omega (d : Fin 2048) (j : Fin 24) :
    spinModulation (griessShortQ (Sum.inr (Sum.inr (d, j)))) 11 = 1 := by
  rw [griessOdd_modulation]
  simp only [Pi.add_apply, sourceWordTheta_low_omega, zero_add]
  have hg : ∀ i : Fin 24, (golayGeneratorBit 11 i : ZMod 2) = 1 := by decide +kernel
  exact hg j

/-- The exact central phase of a preferred pair lift times any odd preferred lift. -/
theorem griessPairOddQ_product_coeff (s : Fin 2) (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    toAdd (griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inr (Sum.inr (d, j)))).coeff =
      if s = 0 then 0 else 1 := by
  change (0 + 0) + ∑ k : Fin 12,
    spinTranslation (griessShortQ (Sum.inl (s, p))) k *
      spinModulation (griessShortQ (Sum.inr (Sum.inr (d, j)))) k = _
  rw [griessPairQ_translation]
  by_cases hs : s = 0
  · simp [hs]
  · simp only [hs, ite_false, zero_add, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact griessOdd_modulation_omega d j

/-- Select the unique pair lift that sends an endpoint odd vector to the other endpoint. -/
noncomputable def griessPairOddColor (p : Fin 276) (d : Fin 2048) : Fin 2 :=
  if (golayEncodedMask d.val).testBit (griessCoordinatePair p).1.val =
      (golayEncodedMask d.val).testBit (griessCoordinatePair p).2.val then 0 else 1

private theorem pairOddColor_binary (p : Fin 276) (d : Fin 2048) :
    ((griessPairOddColor p d).val : ZMod 2) =
      golayBooleanCast ((golayEncodedMask d.val).testBit (griessCoordinatePair p).1.val) +
        golayBooleanCast ((golayEncodedMask d.val).testBit (griessCoordinatePair p).2.val) := by
  cases ha : (golayEncodedMask d.val).testBit (griessCoordinatePair p).1.val <;>
    cases hb : (golayEncodedMask d.val).testBit (griessCoordinatePair p).2.val <;>
    norm_num [griessPairOddColor, ha, hb, golayBooleanCast]
  all_goals decide +kernel

private theorem rotate_mod_two (a b c : ZMod 2) : (a + b) + (c + a) = c + b := by
  calc
    _ = (c + b) + (a + a) := by abel
    _ = _ := by rw [ZModModule.add_self, add_zero]

private theorem pairOddColor_omega (p : Fin 276) (d : Fin 2048) :
    ((griessPairOddColor p d).val : ZMod 2) +
      griessOddOmegaCoefficient d (griessCoordinatePair p).1 =
        griessOddOmegaCoefficient d (griessCoordinatePair p).2 := by
  rw [pairOddColor_binary]
  unfold griessOddOmegaCoefficient
  exact rotate_mod_two _ _ _

private theorem qTranslation_mul (g h : Q) :
    spinTranslation (g * h) = spinTranslation g + spinTranslation h := rfl

private theorem qModulation_mul (g h : Q) :
    spinModulation (g * h) = spinModulation g + spinModulation h := rfl

/-- At the left endpoint the selected actual pair lift has exactly the other odd base. -/
theorem griessPairOddQ_product_base_left (p : Fin 276) (d : Fin 2048) :
    (griessShortQ (Sum.inl (griessPairOddColor p d, p)) *
      griessShortQ (Sum.inr (Sum.inr (d, (griessCoordinatePair p).1)))).base =
        (griessShortQ (Sum.inr (Sum.inr (d, (griessCoordinatePair p).2)))).base := by
  apply (qBase_eq_iff_spin_coordinates _ _).mpr
  constructor
  · rw [qTranslation_mul, griessPairQ_translation_color, griessOdd_translation,
      griessOdd_translation]
    calc
      _ = golayLabelCoefficients ⟨d.val, by omega⟩ +
          (((griessPairOddColor p d).val : ZMod 2) +
            griessOddOmegaCoefficient d (griessCoordinatePair p).1) • Pi.single 11 1 := by
        rw [add_smul]
        abel
      _ = _ := by rw [pairOddColor_omega]
  · rw [qModulation_mul, griessPairQ_modulation, griessOdd_modulation, griessOdd_modulation]
    ext k
    simp only [Pi.add_apply, griessPairSyndrome]
    exact rotate_mod_two _ _ _

/-- At the right endpoint the same actual selected pair lift reverses the odd base. -/
theorem griessPairOddQ_product_base_right (p : Fin 276) (d : Fin 2048) :
    (griessShortQ (Sum.inl (griessPairOddColor p d, p)) *
      griessShortQ (Sum.inr (Sum.inr (d, (griessCoordinatePair p).2)))).base =
        (griessShortQ (Sum.inr (Sum.inr (d, (griessCoordinatePair p).1)))).base := by
  have h := griessPairOddQ_product_base_left p d
  have hs := q_square_base (griessShortQ (Sum.inl (griessPairOddColor p d, p)))
  change _ * _ = _ at h
  change _ * _ = 1 at hs
  change _ * _ = _
  calc
    _ = _ * (_ * _) := by rw [← h]
    _ = _ := by rw [← mul_assoc, hs, one_mul]

/-- The integral pair/odd pairing has only its two indicated physical coordinates. -/
theorem griessPairOdd_integral_pairing (s : Fin 2) (p : Fin 276)
    (d : Fin 2048) (j : Fin 24) :
    leechIntegralPairing (griessShortIntegral (Sum.inl (s, p)))
      (griessShortIntegral (Sum.inr (Sum.inr (d, j)))) =
      4 * griessShortIntegral (Sum.inr (Sum.inr (d, j))) (griessCoordinatePair p).1 +
        (if s = 0 then -4 else 4) *
          griessShortIntegral (Sum.inr (Sum.inr (d, j))) (griessCoordinatePair p).2 := by
  unfold leechIntegralPairing
  simp only [griessShortIntegral, add_mul, Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- An inactive pair lift or a nonendpoint odd coordinate has integral pairing between -8 and 8. -/
theorem griessPairOdd_inactive_pairing_bounds (s : Fin 2) (p : Fin 276)
    (d : Fin 2048) (j : Fin 24)
    (h : s ≠ griessPairOddColor p d ∨
      (j ≠ (griessCoordinatePair p).1 ∧ j ≠ (griessCoordinatePair p).2)) :
    -8 ≤ leechIntegralPairing (griessShortIntegral (Sum.inl (s, p)))
      (griessShortIntegral (Sum.inr (Sum.inr (d, j)))) ∧
    leechIntegralPairing (griessShortIntegral (Sum.inl (s, p)))
      (griessShortIntegral (Sum.inr (Sum.inr (d, j)))) ≤ 8 := by
  rw [griessPairOdd_integral_pairing]
  have hn := griessCoordinatePair_ne p
  simp only [griessShortIntegral]
  fin_cases s <;>
    cases ha : (golayEncodedMask d.val).testBit (griessCoordinatePair p).1.val <;>
    cases hb : (golayEncodedMask d.val).testBit (griessCoordinatePair p).2.val <;>
    by_cases hj1 : j = (griessCoordinatePair p).1 <;>
    by_cases hj2 : j = (griessCoordinatePair p).2 <;>
    simp_all [griessPairOddColor]
  all_goals split_ifs <;> omega

/-- The inactive or nonendpoint pair/odd product has no actual short output base. -/
theorem griessPairOddQ_no_short (s : Fin 2) (p : Fin 276) (d : Fin 2048) (j : Fin 24)
    (h : s ≠ griessPairOddColor p d ∨
      (j ≠ (griessCoordinatePair p).1 ∧ j ≠ (griessCoordinatePair p).2))
    (u : GriessShortIndex) :
    (griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inr (Sum.inr (d, j)))).base ≠
      (griessShortQ u).base := by
  have hb := griessPairOdd_inactive_pairing_bounds s p d j h
  exact griessShortQ_product_base_ne_short _ _ (by omega) (by omega) u

/-- The pair and odd basis labels are always distinct. -/
theorem griessPairOddQ_base_ne_one (s : Fin 2) (p : Fin 276) (d : Fin 2048) (j : Fin 24) :
    (griessShortQ (Sum.inl (s, p)) * griessShortQ (Sum.inr (Sum.inr (d, j)))).base ≠ 1 := by
  intro h
  have he := (griessShortQ_product_base_one_iff
    (Sum.inl (s, p)) (Sum.inr (Sum.inr (d, j)))).mp h
  exact Sum.inl_ne_inr he

/-- The inactive or nonendpoint preferred pair and odd short basis vectors multiply to zero. -/
theorem conwayShortBasis_pairOdd_zero (s : Fin 2) (p : Fin 276) (d : Fin 2048) (j : Fin 24)
    (h : s ≠ griessPairOddColor p d ∨
      (j ≠ (griessCoordinatePair p).1 ∧ j ≠ (griessCoordinatePair p).2)) :
    conwayRawProduct (conwayShortBasis (Sum.inl (s, p)))
      (conwayShortBasis (Sum.inr (Sum.inr (d, j)))) = 0 := by
  rw [conwayRawProduct_shortBasis]
  apply Prod.ext
  · dsimp only
    funext i k
    rw [ite_eq_right (griessPairOddQ_base_ne_one s p d j)]
    rfl
  · apply Prod.ext
    · dsimp only
      funext u
      rw [ite_eq_right (griessPairOddQ_no_short s p d j h u)]
      rfl
    · rfl

/-- The active pair lift sends the left endpoint to the right with its exact phase. -/
theorem conwayShortBasis_pairOdd_left (p : Fin 276) (d : Fin 2048) :
    conwayRawProduct (conwayShortBasis (Sum.inl (griessPairOddColor p d, p)))
      (conwayShortBasis (Sum.inr (Sum.inr (d, (griessCoordinatePair p).1)))) =
      (if griessPairOddColor p d = 0 then (1 : ℝ) else -1) •
        conwayShortBasis (Sum.inr (Sum.inr (d, (griessCoordinatePair p).2))) := by
  rw [conwayRawProduct_shortBasis]
  apply Prod.ext
  · dsimp only
    funext i k
    rw [ite_eq_right (griessPairOddQ_base_ne_one _ p d _)]
    by_cases hc : griessPairOddColor p d = 0 <;> simp [conwayShortBasis, hc]
  · apply Prod.ext
    · dsimp only
      funext u
      simp only [griessPairOddQ_product_base_left, pairEdge_short_base_eq_iff,
        griessPairOddQ_product_coeff]
      simp only [conwayShortBasis, Prod.smul_snd, Prod.smul_fst,
        Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases hc : griessPairOddColor p d = 0 <;>
        by_cases hu : u = Sum.inr (Sum.inr (d, (griessCoordinatePair p).2)) <;>
        simp [hc, hu, eq_comm, qSign_zero, qSign_one]
    · by_cases hc : griessPairOddColor p d = 0 <;> simp [conwayShortBasis, hc]

/-- The active pair lift times the right endpoint gives the left endpoint with the same phase. -/
theorem conwayShortBasis_pairOdd_right (p : Fin 276) (d : Fin 2048) :
    conwayRawProduct (conwayShortBasis (Sum.inl (griessPairOddColor p d, p)))
      (conwayShortBasis (Sum.inr (Sum.inr (d, (griessCoordinatePair p).2)))) =
      (if griessPairOddColor p d = 0 then (1 : ℝ) else -1) •
        conwayShortBasis (Sum.inr (Sum.inr (d, (griessCoordinatePair p).1))) := by
  rw [conwayRawProduct_shortBasis]
  apply Prod.ext
  · dsimp only
    funext i k
    rw [ite_eq_right (griessPairOddQ_base_ne_one _ p d _)]
    by_cases hc : griessPairOddColor p d = 0 <;> simp [conwayShortBasis, hc]
  · apply Prod.ext
    · dsimp only
      funext u
      simp only [griessPairOddQ_product_base_right, pairEdge_short_base_eq_iff,
        griessPairOddQ_product_coeff]
      simp only [conwayShortBasis, Prod.smul_snd, Prod.smul_fst,
        Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases hc : griessPairOddColor p d = 0 <;>
        by_cases hu : u = Sum.inr (Sum.inr (d, (griessCoordinatePair p).1)) <;>
        simp [hc, hu, eq_comm, qSign_zero, qSign_one]
    · by_cases hc : griessPairOddColor p d = 0 <;> simp [conwayShortBasis, hc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

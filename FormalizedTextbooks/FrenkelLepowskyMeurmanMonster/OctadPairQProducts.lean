/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual preferred coordinate-pair multiplication on signed octad classes. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option maxHeartbeats 0 in
-- This tests only the 12-by-12 source generator pairing matrix.
set_option maxRecDepth 10000 in
theorem golaySyndrome_encoder_basis : ∀ j : Fin 12,
    golaySyndrome (golayEncoder (Pi.single j 1)) = 0 := by
  unfold golaySyndrome golayEncoder
  decide +kernel

theorem golaySyndrome_encoder (a : SpinIndex) : golaySyndrome (golayEncoder a) = 0 := by
  have hm : golaySyndrome.comp golayEncoder = 0 := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro j
    simpa only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.zero_apply] using
      golaySyndrome_encoder_basis j
  exact LinearMap.congr_fun hm a

@[simp] theorem griessOctadNegative_local (o : Fin 759) (e : Fin 64) (a : Fin 8) :
    integerParity (griessOctadNegativeInteger o e) (golayOctadCoordinate o a) =
      trialityOctadLocalBit e a := by
  change ((griessOctadNegativeInteger o e (golayOctadCoordinate o a) : ℤ) : ZMod 2) = _
  simp only [griessOctadNegativeInteger, griessOctadSignMask_local,
    trialityOctadLocalBit]
  split_ifs <;> rfl

/-- Preferred pair and octad source sections have zero central product phase. -/
theorem griessPairOctadQ_product_coeff (s : Fin 2) (p : Fin 276) (o : Fin 759) (e : Fin 64) :
    toAdd (griessShortQ (Sum.inl (s,p)) *
      griessShortQ (Sum.inr (Sum.inl (o,e)))).coeff = 0 := by
  rw [griessShortQ_product_coeff_spinDot]
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · rw [griessPairMinus_translation]
    simp [spinDot]
  · rw [griessPairPlus_translation]
    simp only [spinDot, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Pi.single_apply, Finset.mem_univ, ite_true, griessOctad_modulation_last]

/-- Toggling two local signs adds their physical incidence vector; normalizing
by complementation adds the octad codeword, which has zero syndrome. -/
theorem griessOctadNegative_pairFlip (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    integerParity (griessOctadNegativeInteger o (trialityOctadPairFlip a b e)) =
      integerParity (griessOctadNegativeInteger o e) +
        Pi.single (golayOctadCoordinate o a) 1 + Pi.single (golayOctadCoordinate o b) 1 +
          trialityOctadPairComplement a b •
            golayEncoder (golayLabelCoefficients (golayOctadLabel o)) := by
  ext i
  by_cases hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
  · obtain ⟨k, rfl⟩ := golayOctadCoordinate_surjective o i hi
    simp only [Pi.add_apply, griessOctadNegative_local, Pi.single_apply,
      (golayOctadCoordinate_injective o).eq_iff, Pi.smul_apply, smul_eq_mul,
      golayLabelEncoder_boolean, golayOctadCoordinate_mem, golayBooleanCast, ite_true, mul_one]
    exact trialityOctadPairFlip_bit a b e hab k
  · have hs (f : Fin 64) :
        (griessOctadSignMask o f).testBit i.val ≠ true :=
      fun h => hi (griessOctadSignMask_subset o f i h)
    have ha : i ≠ golayOctadCoordinate o a := by
      intro h; subst i; exact hi (golayOctadCoordinate_mem o a)
    have hb : i ≠ golayOctadCoordinate o b := by
      intro h; subst i; exact hi (golayOctadCoordinate_mem o b)
    change ((griessOctadNegativeInteger o (trialityOctadPairFlip a b e) i : ℤ) : ZMod 2) = _
    simp [griessOctadNegativeInteger, hs, integerParity, ha, hb,
      golayLabelEncoder_boolean, hi, golayBooleanCast]

theorem griessOctadNegative_pairFlip_syndrome (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    golaySyndrome (integerParity (griessOctadNegativeInteger o (trialityOctadPairFlip a b e))) =
      golaySyndrome (integerParity (griessOctadNegativeInteger o e)) +
        griessPairSyndrome (griessPairIndex (golayOctadCoordinate o a)
          (golayOctadCoordinate o b) ((golayOctadCoordinate_injective o).ne hab)) := by
  rw [griessOctadNegative_pairFlip o a b e hab, map_add, map_add, map_add,
    map_smul, golaySyndrome_encoder, smul_zero, add_zero]
  rw [add_assoc, ← map_add, ← griessPairIncidence_syndrome, griessPairIncidence_index]

/-- The exact actual short-class label after multiplication by its active coordinate pair. -/
theorem griessPairOctadQ_product_base (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    (griessShortQ (Sum.inl (trialityOctadPairColor a b e,
      griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab))) *
      griessShortQ (Sum.inr (Sum.inl (o,e)))).base =
        (griessShortQ (Sum.inr (Sum.inl (o,trialityOctadPairFlip a b e)))).base := by
  rw [qBase_eq_iff_spin_coordinates, spinTranslation_mul, spinModulation_mul,
    griessPairQ_translation_color, griessPairQ_modulation,
    griessOctad_translation, griessOctad_translation, griessOctad_modulation,
    griessOctad_modulation, trialityOctadPairFlip_omega a b e hab,
    griessOctadNegative_pairFlip_syndrome o a b e hab, add_smul]
  constructor <;> abel

/-- The central coordinate agrees too, so this is equality of the preferred Q lifts. -/
theorem griessPairOctadQ_product (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    griessShortQ (Sum.inl (trialityOctadPairColor a b e,
      griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab))) *
      griessShortQ (Sum.inr (Sum.inl (o,e))) =
        griessShortQ (Sum.inr (Sum.inl (o,trialityOctadPairFlip a b e))) := by
  apply NormalizedCocycleExtension.Extension.ext
  · exact griessPairOctadQ_product_base o a b e hab
  · apply Multiplicative.toAdd.injective
    rw [griessPairOctadQ_product_coeff, griessShortQ_coeff]

set_option backward.isDefEq.respectTransparency false in
/-- The active preferred pair times a signed octad has exactly one short output. -/
theorem conwayRawProduct_pairOctad_active (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) :
    conwayRawProduct (conwayShortBasis (Sum.inl (trialityOctadPairColor a b e,
      griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab))))
      (conwayShortBasis (Sum.inr (Sum.inl (o,e)))) =
        conwayShortBasis (Sum.inr (Sum.inl (o,trialityOctadPairFlip a b e))) := by
  have hprod := griessPairOctadQ_product o a b e hab
  have hb : (griessShortQ (Sum.inl (trialityOctadPairColor a b e,
      griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab))) *
      griessShortQ (Sum.inr (Sum.inl (o,e)))).base ≠ 1 := by
    intro h
    have he := (griessShortQ_product_base_one_iff _ _).mp h
    cases he
  rw [conwayRawProduct_shortBasis]
  simp only [hb, ite_false, griessPairOctadQ_product_coeff, qSign_zero, one_mul]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  ext u
  simp only [hprod, pairEdge_short_base_eq_iff, conwayShortBasis, Pi.single_apply, eq_comm]

/-- Pair coordinates restrict every integral pairing to its two endpoints. -/
theorem griessPair_integral_pairing (s : Fin 2) (p : Fin 276) (v : Fin 24 → ℤ) :
    leechIntegralPairing (griessShortIntegral (Sum.inl (s,p))) v =
      4 * v (griessCoordinatePair p).1 + (if s = 0 then -4 else 4) *
        v (griessCoordinatePair p).2 := by
  unfold leechIntegralPairing
  simp only [griessShortIntegral, add_mul, Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

@[simp] theorem griessOctad_integral_local (o : Fin 759) (e : Fin 64) (a : Fin 8) :
    griessShortIntegral (Sum.inr (Sum.inl (o,e))) (golayOctadCoordinate o a) =
      if (trialityEvenMask e).testBit a.val then -2 else 2 := by
  simp only [griessShortIntegral, golayOctadCoordinate_mem, ite_true, griessOctadSignMask_local]

theorem griessPairOctad_inactive_pairing (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) (s : Fin 2) (hs : s ≠ trialityOctadPairColor a b e) :
    leechIntegralPairing (griessShortIntegral (Sum.inl (s,
      griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab))))
      (griessShortIntegral (Sum.inr (Sum.inl (o,e)))) = 0 := by
  rw [griessPair_integral_pairing, griessPairIndex_coordinates]
  by_cases horder : golayOctadCoordinate o a < golayOctadCoordinate o b
  all_goals simp only [horder, ite_true, ite_false, griessOctad_integral_local]
  all_goals rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  all_goals cases ha : (trialityEvenMask e).testBit a.val
  all_goals cases hb : (trialityEvenMask e).testBit b.val
  all_goals simp_all [trialityOctadPairColor]

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_pairOctad_inactive (o : Fin 759) (a b : Fin 8) (e : Fin 64)
    (hab : a ≠ b) (s : Fin 2) (hs : s ≠ trialityOctadPairColor a b e) :
    conwayRawProduct (conwayShortBasis (Sum.inl (s,
      griessPairIndex (golayOctadCoordinate o a) (golayOctadCoordinate o b)
        ((golayOctadCoordinate_injective o).ne hab))))
      (conwayShortBasis (Sum.inr (Sum.inl (o,e)))) = 0 := by
  have hpair := griessPairOctad_inactive_pairing o a b e hab s hs
  rw [conwayRawProduct_shortBasis_of_pairing _ _ (by rw [hpair]; norm_num)
    (by rw [hpair]; norm_num)]
  simp only [Sum.inl_ne_inr, ite_false]
  rfl

theorem griessOctad_integral_zero (o : Fin 759) (e : Fin 64) (i : Fin 24)
    (hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val ≠ true) :
    griessShortIntegral (Sum.inr (Sum.inl (o,e))) i = 0 := by
  by_contra h
  exact hi ((griessOctad_coordinate_nonzero o e i).mp h)

theorem griessOctad_integral_values (o : Fin 759) (e : Fin 64) (i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inl (o,e))) i = -2 ∨
      griessShortIntegral (Sum.inr (Sum.inl (o,e))) i = 0 ∨
        griessShortIntegral (Sum.inr (Sum.inl (o,e))) i = 2 := by
  simp only [griessShortIntegral]
  split_ifs <;> omega

theorem griessPairOctad_outside_pairing_bounds (s : Fin 2) (p : Fin 276)
    (o : Fin 759) (e : Fin 64)
    (h : (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val ≠ true ∨
      (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).2.val ≠ true) :
    -8 ≤ leechIntegralPairing (griessShortIntegral (Sum.inl (s,p)))
      (griessShortIntegral (Sum.inr (Sum.inl (o,e)))) ∧
    leechIntegralPairing (griessShortIntegral (Sum.inl (s,p)))
      (griessShortIntegral (Sum.inr (Sum.inl (o,e)))) ≤ 8 := by
  rw [griessPair_integral_pairing]
  rcases h with h | h
  · rw [griessOctad_integral_zero o e _ h, mul_zero, zero_add]
    rcases griessOctad_integral_values o e (griessCoordinatePair p).2 with h2 | h2 | h2
    all_goals rw [h2]
    all_goals split_ifs <;> norm_num
  · rw [griessOctad_integral_zero o e _ h, mul_zero, add_zero]
    rcases griessOctad_integral_values o e (griessCoordinatePair p).1 with h1 | h1 | h1
    all_goals rw [h1]
    all_goals norm_num

set_option backward.isDefEq.respectTransparency false in
theorem conwayRawProduct_pairOctad_outside (s : Fin 2) (p : Fin 276)
    (o : Fin 759) (e : Fin 64)
    (h : (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val ≠ true ∨
      (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).2.val ≠ true) :
    conwayRawProduct (conwayShortBasis (Sum.inl (s,p)))
      (conwayShortBasis (Sum.inr (Sum.inl (o,e)))) = 0 := by
  have hb := griessPairOctad_outside_pairing_bounds s p o e h
  rw [conwayRawProduct_shortBasis_of_pairing _ _ (by omega) (by omega)]
  simp only [Sum.inl_ne_inr, ite_false]
  rfl
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

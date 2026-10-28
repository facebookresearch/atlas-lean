/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Same-octad products have only diagonal and A/B/C dictionary output. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The Parker source theta has no all-one cocode coordinate. -/
theorem sourceWordTheta_last (d : Fin 4096) : sourceWordTheta d 11 = 0 := by
  have hb : ∀ j : Fin 12, sourceCodeTheta j 11 = 0 := by decide +kernel
  have ha : ∀ i j : Fin 12,
      golayBooleanCast ((parkerBasisAssociatorMasks i j).testBit 11) = 0 := by decide +kernel
  change golayBooleanCast ((parkerThetaMask d.val).testBit 11) = 0
  apply (sourceCodeThetaPolynomial_mask d (11 : Fin 12)).trans
  simp only [sourceCodeThetaPolynomial, hb, show (11 : Fin 12).val = 11 by decide,
    ha, mul_zero, ite_self,
    Finset.sum_const_zero, zero_add]

theorem griessOctad_modulation_last (o : Fin 759) (e : Fin 64) :
    spinModulation (griessShortQ (Sum.inr (Sum.inl (o,e)))) 11 = 0 := by
  rw [griessOctad_modulation]
  change sourceWordTheta (golayOctadLabel o) 11 +
    golaySyndrome (integerParity (griessOctadNegativeInteger o e)) 11 = 0
  rw [sourceWordTheta_last]
  change 0 + (∑ i, integerParity (griessOctadNegativeInteger o e) i *
    (golayGeneratorBit 11 i : ZMod 2)) = 0
  simp only [golayGeneratorBit_all_one, Int.cast_one, mul_one, zero_add]
  exact griessOctadNegative_parity_sum o e

theorem griessOdd_modulation_last (d : Fin 2048) (j : Fin 24) :
    spinModulation (griessShortQ (Sum.inr (Sum.inr (d,j)))) 11 = 1 := by
  rw [griessOdd_modulation]
  change sourceWordTheta ⟨d.val, by omega⟩ 11 + (golayGeneratorBit 11 j : ZMod 2) = 1
  rw [sourceWordTheta_last, golayGeneratorBit_all_one]
  simp

/-- Same-octad preferred products cannot have an odd-vector output class. -/
theorem griessOctadQ_product_ne_odd (o : Fin 759) (e f : Fin 64)
    (d : Fin 2048) (j : Fin 24) :
    (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inl (o,f)))).base ≠
        (griessShortQ (Sum.inr (Sum.inr (d,j)))).base := by
  intro h
  have hm := congrArg (fun v : Multiplicative (Fin 24 → ZMod 2) =>
    toAdd v (Fin.natAdd 12 (11 : Fin 12))) h
  change spinModulation (griessShortQ (Sum.inr (Sum.inl (o,e))) *
    griessShortQ (Sum.inr (Sum.inl (o,f)))) 11 =
      spinModulation (griessShortQ (Sum.inr (Sum.inr (d,j)))) 11 at hm
  rw [spinModulation_mul, Pi.add_apply, griessOctad_modulation_last,
    griessOctad_modulation_last, griessOdd_modulation_last, zero_add] at hm
  exact zero_ne_one hm

/-- Characteristic-two cancellation for a code vector with three Ω corrections. -/
theorem octad_translation_cancellation (a b w : SpinIndex) (u v t : ZMod 2)
    (h : (a + u • w) + (a + v • w) = b + t • w) :
    b = (u + v + t) • w := by
  have hh : (a + u • w) + (a + v • w) = (u + v) • w := by
    rw [add_smul]
    calc
      _ = (a + a) + (u • w + v • w) := by abel
      _ = _ := by rw [ZModModule.add_self, zero_add]
  rw [hh] at h
  have hc := congrArg (fun x => x + t • w) h
  rw [add_smul]
  calc
    b = (b + t • w) + t • w := by
      rw [add_assoc, ZModModule.add_self, add_zero]
    _ = (u + v) • w + t • w := hc.symm

/-- An octad codeword cannot be zero or the all-one word. -/
theorem golayOctad_coefficients_ne_omega_smul (p : Fin 759) (a : ZMod 2) :
    golayLabelCoefficients (golayOctadLabel p) ≠ a • Pi.single 11 1 := by
  intro h
  have hw : (∑ i, (golayEncoder (golayLabelCoefficients (golayOctadLabel p)) i).val) = 8 := by
    simp_rw [golayLabelEncoder_match]
    exact (by simpa only [golayMaskWeight, golayMaskSupport_card] using golayOctad_support_card p)
  have he := congrArg golayEncoder h
  rw [map_smul, golay_all_one] at he
  rw [he] at hw
  fin_cases a <;> norm_num [Pi.smul_apply, show (1 : ZMod 2).val = 1 by decide] at hw

/-- Same-octad preferred products cannot have any octad output class. -/
theorem griessOctadQ_product_ne_octad (o p : Fin 759) (e f g : Fin 64) :
    (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inl (o,f)))).base ≠
        (griessShortQ (Sum.inr (Sum.inl (p, g)))).base := by
  intro h
  have ht : spinTranslation (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inl (o,f)))) =
        spinTranslation (griessShortQ (Sum.inr (Sum.inl (p, g)))) := by
    funext k
    exact congrArg (fun v : Multiplicative (Fin 24 → ZMod 2) => toAdd v (Fin.castAdd 12 k)) h
  rw [spinTranslation_mul, griessOctad_translation, griessOctad_translation,
    griessOctad_translation] at ht
  have hc := octad_translation_cancellation _ _ (Pi.single 11 1)
    (griessOctadOmegaCoefficient e) (griessOctadOmegaCoefficient f)
      (griessOctadOmegaCoefficient g) ht
  exact golayOctad_coefficients_ne_omega_smul p _ hc

/-- The decoder's octad block is exactly the raw signed-octad short coordinates. -/
theorem griessConwayDecode_octad_block (x : ConwayRawSpace) :
    (trialityBlocksEquiv (griessConwayDecode x)).2.2.1 =
      fun p g => x.2.1 (Sum.inr (Sum.inl (p, g))) := by
  simp only [griessConwayDecode, LinearEquiv.apply_symm_apply]

/-- With zero raw tensor coordinates, only the odd-short X component remains. -/
theorem griessConwayDecode_short_XYZ_block (M : Matrix (Fin 24) (Fin 24) ℝ)
    (S : GriessShortIndex → ℝ) :
    (trialityBlocksEquiv (griessConwayDecode (M, (S,0)))).2.2.2 =
      fun s k => if s = 0 then S (Sum.inr (Sum.inr (finProdFinEquiv.symm k))) else 0 := by
  simp only [griessConwayDecode, LinearEquiv.apply_symm_apply]
  funext s k
  split_ifs <;> simp

/-- Generic sparse short product has zero octad block when no output base is an octad. -/
theorem conwayShortBasisProduct_octad_zero (r s : GriessShortIndex)
    (h : ∀ p g, (griessShortQ r * griessShortQ s).base ≠
      (griessShortQ (Sum.inr (Sum.inl (p, g)))).base) :
    (trialityBlocksEquiv (griessConwayDecode
      (conwayRawProduct (conwayShortBasis r) (conwayShortBasis s)))).2.2.1 = 0 := by
  rw [conwayRawProduct_shortBasis, griessConwayDecode_octad_block]
  funext p g
  simp only [h p g, ite_false, Pi.zero_apply]

/-- The octad output block of two basis vectors from one octad is zero. -/
theorem griessProd_sameOctad_octad_zero (o : Fin 759) (e f : Fin 64) :
    (trialityBlocksEquiv (griessProd (trialityOctadBasis o e)
      (trialityOctadBasis o f))).2.2.1 = 0 := by
  rw [griessProd_octadBasis]
  exact conwayShortBasisProduct_octad_zero _ _ (fun p g =>
    griessOctadQ_product_ne_octad o p e f g)

/-- The X/Y/Z output block of two basis vectors from one octad is zero. -/
theorem griessProd_sameOctad_XYZ_zero (o : Fin 759) (e f : Fin 64) :
    (trialityBlocksEquiv (griessProd (trialityOctadBasis o e)
      (trialityOctadBasis o f))).2.2.2 = 0 := by
  rw [griessProd_octadBasis, conwayRawProduct_shortBasis, griessConwayDecode_short_XYZ_block]
  funext s k
  by_cases hs : s = 0
  · rw [ite_eq_left hs]
    exact ite_eq_right (griessOctadQ_product_ne_odd o e f (finProdFinEquiv.symm k).1
      (finProdFinEquiv.symm k).2)
  · exact ite_eq_right hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Vanishing actual octad cubics away from their codeword support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCubic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem binary_complement_weight (a : ZMod 2) :
    (a + 1).val + a.val = 1 := by
  fin_cases a <;> decide +kernel

private theorem binary_scalar_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> norm_num

/-- A weight-eight codeword cannot differ from another weight-eight word by Ω. -/
theorem golayOctad_sum_ne_complement (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) :
    golayOctadWord u ≠ golayOctadWord o + golayOctadWord p + (fun _ => 1) := by
  intro h
  have hw := golayOctad_sum_weight o p
  rw [hfour] at hw
  have hs : (∑ i, (golayOctadWord u i).val) +
      (∑ i, ((golayOctadWord o + golayOctadWord p) i).val) = 24 := by
    rw [← Finset.sum_add_distrib]
    simp only [h, Pi.add_apply]
    simp_rw [binary_complement_weight]
    norm_num
  rw [golayOctadWord_weight] at hs
  omega

/-- Preferred-Q equality forces the expected octad word; the possible Ω
correction is excluded by the physical weights, without label conventions. -/
theorem griessOctadQ_base_eq_implies_word_sum (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (h : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inl (p, f)))).base =
        (griessShortQ (Sum.inr (Sum.inl (u, g)))).base) :
    golayOctadWord u = golayOctadWord o + golayOctadWord p := by
  have ht : spinTranslation (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inl (p, f)))) =
        spinTranslation (griessShortQ (Sum.inr (Sum.inl (u, g)))) := by
    funext k
    exact congrArg (fun v : Multiplicative (Fin 24 → ZMod 2) =>
      toAdd v (Fin.castAdd 12 k)) h
  rw [griessOctadQ_cross_product_translation, griessOctad_translation] at ht
  have hc : golayLabelCoefficients (golayOctadLabel u) =
      (golayLabelCoefficients (golayOctadLabel o) +
        golayLabelCoefficients (golayOctadLabel p)) +
      (griessOctadOmegaCoefficient e + griessOctadOmegaCoefficient f +
        griessOctadOmegaCoefficient g) • Pi.single 11 1 := by
    have hh := congrArg (fun v : SpinIndex =>
      v + griessOctadOmegaCoefficient g • Pi.single 11 1) ht
    simpa only [add_assoc, ZModModule.add_self, add_zero, add_smul] using hh.symm
  have he := congrArg golayEncoder hc
  simp only [map_add, map_smul, golay_all_one] at he
  change golayOctadWord u = golayOctadWord o + golayOctadWord p +
    (griessOctadOmegaCoefficient e + griessOctadOmegaCoefficient f +
      griessOctadOmegaCoefficient g) • (fun _ => 1) at he
  rcases binary_scalar_cases (griessOctadOmegaCoefficient e + griessOctadOmegaCoefficient f +
    griessOctadOmegaCoefficient g) with hz | ho
  · rw [hz, zero_smul, add_zero] at he
    exact he
  · rw [ho, one_smul] at he
    exact False.elim (golayOctad_sum_ne_complement o p u hfour he)

/-- Actual O×O×O coefficients vanish outside the unique sum octad. -/
theorem griessForm_octad_cubic_zero (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hword : golayOctadWord u ≠ golayOctadWord o + golayOctadWord p) :
    griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
      (trialityOctadBasis u g) = 0 := by
  rw [griessForm_octad_cubic]
  exact ite_eq_right (fun h => hword (griessOctadQ_base_eq_implies_word_sum o p u e f g hfour h))

/-- The Fourier-transformed cubic has the same zero codeword support. -/
theorem griessForm_transformed_octad_cubic_zero (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hword : golayOctadWord u ≠ golayOctadWord o + golayOctadWord p) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityOctadBasis p f))) (sExtra (trialityOctadBasis u g)) = 0 := by
  rw [griessForm_transformed_octad_cubic]
  simp only [griessForm_octad_cubic_zero o p u _ _ _ hfour hword,
    mul_zero, Finset.sum_const_zero]

/-- Arbitrary octad products cannot have an odd-short output. -/
theorem griessOctadQ_cross_product_ne_odd (o p : Fin 759) (e f : Fin 64)
    (d : Fin 2048) (j : Fin 24) :
    (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inl (p, f)))).base ≠
        (griessShortQ (Sum.inr (Sum.inr (d, j)))).base := by
  intro h
  have hm := congrArg (fun v : Multiplicative (Fin 24 → ZMod 2) =>
    toAdd v (Fin.natAdd 12 (11 : Fin 12))) h
  change spinModulation (griessShortQ (Sum.inr (Sum.inl (o, e))) *
    griessShortQ (Sum.inr (Sum.inl (p, f)))) 11 =
      spinModulation (griessShortQ (Sum.inr (Sum.inr (d, j)))) 11 at hm
  rw [spinModulation_mul, Pi.add_apply, griessOctad_modulation_last,
    griessOctad_modulation_last, griessOdd_modulation_last, zero_add] at hm
  exact zero_ne_one hm

/-- Every two octad basis vectors have zero X/Y/Z output block. -/
theorem griessProd_octad_XYZ_zero (o p : Fin 759) (e f : Fin 64) :
    (trialityBlocksEquiv (griessProd (trialityOctadBasis o e)
      (trialityOctadBasis p f))).2.2.2 = 0 := by
  rw [griessProd_octadBasis, conwayRawProduct_shortBasis, griessConwayDecode_short_XYZ_block]
  funext s k
  by_cases hs : s = 0
  · rw [ite_eq_left hs]
    exact ite_eq_right (griessOctadQ_cross_product_ne_odd o p e f
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  · exact ite_eq_right hs

/-- The actual cubic with two octads and any X/Y/Z tester is zero. -/
theorem griessForm_octad_octad_XYZ_zero (o p : Fin 759) (e f : Fin 64)
    (s : Fin 3) (k : Fin 49152) :
    griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
      (trialityXYZBasis s k) = 0 := by
  rw [griessForm_eq_trialityBlockForm, trialityXYZBasis_blocks]
  simp only [trialityBlockForm, griessProd_octad_XYZ_zero, Pi.zero_apply,
    zero_mul, mul_zero, Finset.sum_const_zero, mul_zero, add_zero]

/-- Fourier transforms on the octads and triality on the tester preserve this
zero cubic, by bilinearity and the exact source basis formulas. -/
theorem griessForm_transformed_octad_octad_XYZ_zero (o p : Fin 759) (e f : Fin 64)
    (s : Fin 3) (k : Fin 49152) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityOctadBasis p f))) (sExtra (trialityXYZBasis s k)) = 0 := by
  rw [griessProd_transformed_octad_sum, sExtra_XYZ_basis]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, griessForm_octad_octad_XYZ_zero, mul_zero, Finset.sum_const_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

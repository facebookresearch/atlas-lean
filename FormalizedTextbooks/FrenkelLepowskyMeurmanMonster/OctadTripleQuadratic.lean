/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual half-weight parity for three signed octads on a four-point intersection. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadAffineSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.BinaryTripleQuadratic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCubic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The binary negative-pattern weight is its actual eight-coordinate weight. -/
theorem griessOctadNegative_binary_weight (o : Fin 759) (e : Fin 64) :
    (∑ i, (integerParity (griessOctadNegativeInteger o e) i).val) =
      trialityBitWeight8 (trialityEvenMask e) := by
  calc
    _ = golayMaskWeight (griessOctadSignMask o e) := by
      apply Finset.sum_congr rfl
      intro i _
      cases hb : (griessOctadSignMask o e).testBit i.val <;>
        norm_num [integerParity, griessOctadNegativeInteger, hb,
          show (1 : ZMod 2).val = 1 by decide]
    _ = _ := griessOctadSignMask_weight o e

/-- Even row weights with total divisible by four have zero total half-weight parity. -/
theorem binary_half_weight_three_zero (a b c : ℕ)
    (ha : 2 ∣ a) (hb : 2 ∣ b) (hc : 2 ∣ c) (hfour : 4 ∣ a + b + c) :
    ((a / 2 : ℕ) : ZMod 2) + ((b / 2 : ℕ) : ZMod 2) + ((c / 2 : ℕ) : ZMod 2) = 0 := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  obtain ⟨z,hz⟩ := hc
  obtain ⟨k,hk⟩ := hfour
  have hs : a / 2 + b / 2 + c / 2 = 2 * k := by omega
  calc
    _ = ((a / 2 + b / 2 + c / 2 : ℕ) : ZMod 2) := by push_cast; rfl
    _ = 0 := by rw [hs]; simp [show (2 : ZMod 2) = 0 by decide]

/-- The actual intersection weight is its physical intersection cardinality. -/
theorem golayOctad_intersection_binary_weight (o p : Fin 759) :
    (∑ i, (golayOctadWord o i * golayOctadWord p i).val) =
      (golayOctadIntersection o p).card := by
  have hpoint (i : Fin 24) :
      (golayOctadWord o i * golayOctadWord p i).val =
        if i ∈ golayOctadIntersection o p then 1 else 0 := by
    simp only [golayOctadIntersection_support, Finset.mem_inter,
      ← golayOctadWord_ne_zero_iff]
    generalize golayOctadWord o i = a
    generalize golayOctadWord p i = b
    fin_cases a <;> fin_cases b <;> decide +kernel
  simp_rw [hpoint]
  simp

/-- The actual half-weight correction is exactly the local quadratic diagonal sign. -/
theorem qSign_griessOctadOmega (e : Fin 64) :
    qSign (griessOctadOmegaCoefficient e) = (trialityIntegerDiagonal e : ℝ) := by
  unfold qSign griessOctadOmegaCoefficient trialityIntegerDiagonal
  simp only [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  split_ifs <;> norm_num

/-- The intrinsic syndrome condition already forces the three actual
signed-octad half-weight corrections to sum to zero. -/
theorem griessOctad_triple_omega_four (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (hs : golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
      integerParity (griessOctadNegativeInteger p f) +
      integerParity (griessOctadNegativeInteger u g)) =
        golaySyndrome (fun i => golayOctadWord o i * golayOctadWord p i)) :
    griessOctadOmegaCoefficient e + griessOctadOmegaCoefficient f +
      griessOctadOmegaCoefficient g = 0 := by
  have hop : o ≠ p := by
    intro h
    subst p
    rw [golayOctadIntersection_support, Finset.inter_self,
      golayOctadSupport_card] at hfour
    omega
  have ha := (griessOctad_triple_syndrome_four o p u e f g hop hfour hu).mp hs
  have hn (v : Fin 759) (a : Fin 64) (i : Fin 24) (hi : golayOctadWord v i = 0) :
      integerParity (griessOctadNegativeInteger v a) i = 0 := by
    apply griessOctadNegative_supported
    simp only [← golayOctadWord_ne_zero_iff, hi, ne_eq, not_true_eq_false,
      not_false_eq_true]
  have hdiv := binaryTripleQuarterWeight (golayOctadWord o) (golayOctadWord p)
    (integerParity (griessOctadNegativeInteger o e))
    (integerParity (griessOctadNegativeInteger p f))
    (integerParity (griessOctadNegativeInteger u g))
    (hn o e) (hn p f) (fun i hi => hn u g i (by rw [hu]; exact hi))
    (by rw [griessOctadNegative_binary_weight]; exact trialityEvenMask_even e)
    (by rw [griessOctadNegative_binary_weight]; exact trialityEvenMask_even f)
    (by rw [griessOctadNegative_binary_weight]; exact trialityEvenMask_even g)
    (golayOctadWord_weight o) (golayOctadWord_weight p)
    (by rw [golayOctad_intersection_binary_weight]; exact hfour) ha
  rw [griessOctadNegative_binary_weight, griessOctadNegative_binary_weight,
    griessOctadNegative_binary_weight] at hdiv
  exact binary_half_weight_three_zero _ _ _ (trialityEvenMask_even e)
    (trialityEvenMask_even f) (trialityEvenMask_even g) hdiv

/-- The actual four-point octad cubic has a single intrinsic affine support
condition; its half-weight parity condition follows from that condition. -/
theorem griessForm_octad_cubic_four_syndrome (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
      (trialityOctadBasis u g) =
        if golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
          integerParity (griessOctadNegativeInteger p f) +
          integerParity (griessOctadNegativeInteger u g)) =
            golaySyndrome (fun i => golayOctadWord o i * golayOctadWord p i) then
          qSign (spinDot (sourceWordTheta (golayOctadLabel p))
            (golayLabelCoefficients (golayOctadLabel o)) +
            ∑ i, integerParity (griessOctadNegativeInteger p f) i * golayOctadWord o i)
        else 0 := by
  have hcode : golayLabelCoefficients (golayOctadLabel u) =
      golayLabelCoefficients (golayOctadLabel o) +
        golayLabelCoefficients (golayOctadLabel p) := by
    apply golayEncoder_injective
    rw [map_add]
    exact hu
  rw [griessForm_octad_cubic_source o p u e f g hcode]
  change (if (_ ∧ _) then _ else _) = _
  by_cases hs : golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
      integerParity (griessOctadNegativeInteger p f) +
      integerParity (griessOctadNegativeInteger u g)) =
        golaySyndrome (fun i => golayOctadWord o i * golayOctadWord p i)
  · have ho := griessOctad_triple_omega_four o p u e f g hfour hu hs
    simp only [golayOctadWord] at hs ⊢
    simp only [hs, ho, and_self, ite_true]
  · simp only [golayOctadWord] at hs ⊢
    simp only [hs, and_false, ite_false]

/-- The triple quadratic diagonal is one on the actual cubic's affine support. -/
theorem griessOctad_triple_diagonal_four (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p)
    (hs : golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
      integerParity (griessOctadNegativeInteger p f) +
      integerParity (griessOctadNegativeInteger u g)) =
        golaySyndrome (fun i => golayOctadWord o i * golayOctadWord p i)) :
    (trialityIntegerDiagonal e : ℝ) * (trialityIntegerDiagonal f : ℝ) *
      (trialityIntegerDiagonal g : ℝ) = 1 := by
  rw [← qSign_griessOctadOmega, ← qSign_griessOctadOmega, ← qSign_griessOctadOmega,
    ← qSign_add, ← qSign_add, griessOctad_triple_omega_four o p u e f g hfour hu hs,
    qSign_zero]

/-- The Fourier quadratic row factors cancel on every actual four-point octad cubic. -/
theorem griessForm_octad_cubic_four_diagonal (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    ((trialityIntegerDiagonal e : ℝ) * (trialityIntegerDiagonal f : ℝ) *
      (trialityIntegerDiagonal g : ℝ)) *
      griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
        (trialityOctadBasis u g) =
      griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
        (trialityOctadBasis u g) := by
  rw [griessForm_octad_cubic_four_syndrome o p u e f g hfour hu]
  split_ifs with hs
  · rw [griessOctad_triple_diagonal_four o p u e f g hfour hu hs, one_mul]
  · exact mul_zero _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

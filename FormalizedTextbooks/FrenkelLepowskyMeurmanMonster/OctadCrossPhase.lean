/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual cross-octad preferred-Q phases in the source code/cocode coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairEdgeQProducts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The singleton translation character extracts its modulation coordinate. -/
theorem spinDot_single_right (b : SpinIndex) (j : Fin 12) :
    spinDot b (Pi.single j 1) = b j := by
  simp [spinDot, Pi.single_apply]

/-- Parker theta contributes no character on the all-one translation. -/
theorem sourceWordTheta_dot_omega (d : Fin 4096) :
    spinDot (sourceWordTheta d) (Pi.single 11 1) = 0 := by
  rw [spinDot_single_right, sourceWordTheta_last]

/-- The preferred-Q phase for arbitrary two octads is the code/theta character
and the parity of the second negative subset in the first octad. It is independent
of the first sign pattern, including its possible Ω correction. -/
theorem griessOctadQ_cross_product_coeff (o p : Fin 759) (e f : Fin 64) :
    toAdd (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inl (p,f)))).coeff =
        spinDot (sourceWordTheta (golayOctadLabel p))
          (golayLabelCoefficients (golayOctadLabel o)) +
          ∑ i, integerParity (griessOctadNegativeInteger p f) i *
            golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i := by
  rw [griessShortQ_product_coeff_spinDot, griessOctad_modulation, griessOctad_translation,
    spinDot_add_left, spinDot_add_right, spinDot_add_right,
    spinDot_smul_right, spinDot_smul_right, sourceWordTheta_dot_omega,
    griessOctadNegative_dot_omega]
  simp only [mul_zero, add_zero, golaySyndrome_spinDot]

/-- The actual product modulation for arbitrary two signed octads. -/
theorem griessOctadQ_cross_product_modulation (o p : Fin 759) (e f : Fin 64) :
    spinModulation (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inl (p,f)))) =
        (sourceWordTheta (golayOctadLabel o) + sourceWordTheta (golayOctadLabel p)) +
          (golaySyndrome (integerParity (griessOctadNegativeInteger o e)) +
            golaySyndrome (integerParity (griessOctadNegativeInteger p f))) := by
  rw [spinModulation_mul, griessOctad_modulation, griessOctad_modulation]
  exact (show ∀ a b c d : SpinIndex, (a + b) + (c + d) = (a + c) + (b + d) from
    by intros; abel) _ _ _ _

/-- The actual product translation for arbitrary two signed octads. -/
theorem griessOctadQ_cross_product_translation (o p : Fin 759) (e f : Fin 64) :
    spinTranslation (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inl (p,f)))) =
        (golayLabelCoefficients (golayOctadLabel o) +
          golayLabelCoefficients (golayOctadLabel p)) +
          (griessOctadOmegaCoefficient e + griessOctadOmegaCoefficient f) • Pi.single 11 1 := by
  rw [spinTranslation_mul, griessOctad_translation, griessOctad_translation, add_smul]
  exact (show ∀ a b c d : SpinIndex, (a + b) + (c + d) = (a + c) + (b + d) from
    by intros; abel) _ _ _ _

/-- The actual Parker word theta is the proved quadratic polynomial. -/
theorem sourceWordTheta_eq_polynomial (d : Fin 4096) :
    sourceWordTheta d = sourceCodeThetaPolynomial (golayLabelCoefficients d) := by
  funext k
  exact sourceCodeThetaPolynomial_mask d k

/-- Source code addition supplies precisely the physical intersection syndrome. -/
theorem sourceWordTheta_add (d e f : Fin 4096)
    (h : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    sourceWordTheta f = sourceWordTheta d + sourceWordTheta e +
      golaySyndrome (fun i => golayEncoder (golayLabelCoefficients d) i *
        golayEncoder (golayLabelCoefficients e) i) := by
  rw [sourceWordTheta_eq_polynomial, sourceWordTheta_eq_polynomial,
    sourceWordTheta_eq_polynomial, h, sourceCodeThetaPolynomial_add]

/-- Characteristic-two rearrangement of an additive coordinate equation. -/
theorem source_add_eq_add_iff {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (x y z : A) : x = y + z ↔ x + z = y := by
  constructor
  · intro h
    rw [h, add_assoc, ZModModule.add_self, add_zero]
  · intro h
    have hc := congrArg (fun a => a + z) h
    simpa only [add_assoc, ZModModule.add_self, add_zero] using hc

/-- Multiplication by the all-one singleton is injective on its binary coefficient. -/
theorem source_omega_smul_eq_iff (a b : ZMod 2) :
    a • (Pi.single 11 1 : SpinIndex) = b • Pi.single 11 1 ↔ a = b := by
  constructor
  · intro h
    have hc := congrFun h 11
    simpa only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] using hc
  · rintro rfl
    rfl

/-- For three source octads whose code labels add, actual Q-base closure is
exactly the Ω-parity condition and the physical intersection-cocode condition. -/
theorem griessOctadQ_triple_base_iff (o p u : Fin 759) (e f g : Fin 64)
    (hcode : golayLabelCoefficients (golayOctadLabel u) =
      golayLabelCoefficients (golayOctadLabel o) + golayLabelCoefficients (golayOctadLabel p)) :
    (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inl (p,f)))).base =
        (griessShortQ (Sum.inr (Sum.inl (u,g)))).base ↔
      (griessOctadOmegaCoefficient e + griessOctadOmegaCoefficient f +
        griessOctadOmegaCoefficient g = 0) ∧
      golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
        integerParity (griessOctadNegativeInteger p f) +
        integerParity (griessOctadNegativeInteger u g)) =
          golaySyndrome (fun i => golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i *
            golayEncoder (golayLabelCoefficients (golayOctadLabel p)) i) := by
  rw [qBase_eq_iff_spin_coordinates, griessOctadQ_cross_product_translation,
    griessOctad_translation, griessOctadQ_cross_product_modulation,
    griessOctad_modulation, sourceWordTheta_add _ _ _ hcode, hcode,
    add_assoc (sourceWordTheta (golayOctadLabel o) + sourceWordTheta (golayOctadLabel p)),
    add_left_cancel_iff, add_left_cancel_iff, source_omega_smul_eq_iff,
    pairEdge_add_eq_iff_triple]
  rw [source_add_eq_add_iff]
  simp only [map_add]


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.MeasureTheory.Measure.RadonProduct.Fubini
public import MathlibExt.Topology.Algebra.Group.DiagonalShear
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CompactSupport
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral

/-!
# The actual LCA Haar-square coordinate shear unitary

Reverse compact-support integration and the original Haar invariance prove
that `(s,t) ↦ (s*t⁻¹,t)` preserves the actual Borel Radon square measure.
Its original inverse `(r,t) ↦ (r*t,t)` then gives a literal linear isometry
equivalence on the full Hilbert-valued product L2 space. Both operator
directions retain their original a.e. coordinates and compact-support values.

The original LCA/LCH/Borel/regular-Haar hypotheses and independent Hilbert
universe are retained. H may be zero. No countability, s-finiteness,
supplied unitary or desired spatial model is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory
open scoped CompactlySupported CStarAlgebra

namespace MeasureTheory

noncomputable section

universe uG uH

variable {G : Type uG} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- The actual Borel measurable space of the original topological Haar square. -/
local instance instExactShearProductMeasurableSpace : MeasurableSpace (G × G) := borel (G × G)
local instance instExactShearProductBorelSpace : BorelSpace (G × G) := ⟨rfl⟩

namespace Measure

omit [μ.Regular] in
/-- The literal original difference-coordinate shear preserves the actual Borel Radon square. -/
theorem map_diagonalDifferenceShear_radonProd :
    Measure.map (Homeomorph.diagonalDifferenceShear G) (radonProd μ μ) = radonProd μ μ := by
  let e := Homeomorph.diagonalDifferenceShear G
  change Measure.map e (radonProd μ μ) = radonProd μ μ
  let _ : (Measure.map e (radonProd μ μ)).Regular := Measure.Regular.map e
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [e.measurableEmbedding.integral_map]
  let F : C_c(G × G, ℝ) :=
    ⟨⟨fun z => f (e z), f.continuous.comp e.continuous⟩,
      f.hasCompactSupport.comp_homeomorph e⟩
  change (∫ z : G × G, F z ∂(radonProd μ μ)) =
    ∫ z : G × G, f z ∂(radonProd μ μ)
  rw [integral_radonProd_swap μ μ F, integral_radonProd_swap μ μ f]
  change (∫ t : G, ∫ s : G, f (s * t⁻¹, t) ∂μ ∂μ) =
    ∫ t : G, ∫ s : G, f (s, t) ∂μ ∂μ
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    simpa only [mul_comm] using
      integral_mul_left_eq_self (μ := μ) (fun s : G => f (s, t)) t⁻¹

omit [μ.Regular] in
/-- The actual forward coordinate shear is measure preserving on the full Borel Radon square. -/
theorem measurePreserving_diagonalDifferenceShear_radonProd :
    MeasurePreserving (Homeomorph.diagonalDifferenceShear G)
      (radonProd μ μ) (radonProd μ μ) :=
  ⟨(Homeomorph.diagonalDifferenceShear G).measurable,
    map_diagonalDifferenceShear_radonProd μ⟩

omit [μ.Regular] in
/-- The original inverse coordinate shear is also measure preserving on the same actual carrier. -/
theorem measurePreserving_diagonalDifferenceShear_symm_radonProd :
    MeasurePreserving (Homeomorph.diagonalDifferenceShear G).symm
      (radonProd μ μ) (radonProd μ μ) :=
  MeasurePreserving.symm (Homeomorph.diagonalDifferenceShear G).toMeasurableEquiv
    (measurePreserving_diagonalDifferenceShear_radonProd μ)

end Measure

namespace HaarL2

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual inverse-shear pullback and its literal forward-shear inverse on full H-valued Radon L2. -/
def diagonalShearIsometry :
    Lp H 2 (Measure.radonProd μ μ) ≃ₗᵢ[ℂ] Lp H 2 (Measure.radonProd μ μ) := by
  let e := Homeomorph.diagonalDifferenceShear G
  let hE := Measure.measurePreserving_diagonalDifferenceShear_radonProd μ
  let hInv := Measure.measurePreserving_diagonalDifferenceShear_symm_radonProd μ
  exact
    { toFun := Lp.compMeasurePreserving e.symm hInv
      invFun := Lp.compMeasurePreserving e hE
      left_inv ξ := by
        change Lp.compMeasurePreserving e hE (Lp.compMeasurePreserving e.symm hInv ξ) = ξ
        apply Lp.ext
        have hQ : QuasiMeasurePreserving e (Measure.radonProd μ μ) (Measure.radonProd μ μ) :=
          hE.quasiMeasurePreserving
        filter_upwards [Lp.coeFn_compMeasurePreserving
            (Lp.compMeasurePreserving e.symm hInv ξ) hE,
          hQ.ae_eq_comp (Lp.coeFn_compMeasurePreserving ξ hInv)] with z h₁ h₂
        exact h₁.trans (h₂.trans (congrArg (fun w : G × G => ξ w) (e.symm_apply_apply z)))
      right_inv ξ := by
        change Lp.compMeasurePreserving e.symm hInv (Lp.compMeasurePreserving e hE ξ) = ξ
        apply Lp.ext
        have hQ : QuasiMeasurePreserving e.symm (Measure.radonProd μ μ) (Measure.radonProd μ μ) :=
          hInv.quasiMeasurePreserving
        filter_upwards [Lp.coeFn_compMeasurePreserving
            (Lp.compMeasurePreserving e hE ξ) hInv,
          hQ.ae_eq_comp (Lp.coeFn_compMeasurePreserving ξ hE)] with z h₁ h₂
        exact h₁.trans (h₂.trans (congrArg (fun w : G × G => ξ w) (e.apply_symm_apply z)))
      map_add' ξ η := (Lp.compMeasurePreserving e.symm hInv).map_add ξ η
      map_smul' c ξ := (Lp.compMeasurePreservingₗ ℂ e.symm hInv).map_smul c ξ
      norm_map' ξ := Lp.norm_compMeasurePreserving ξ hInv }

omit [CompleteSpace H] [μ.Regular] in
/-- The actual full L2 shear has the literal inverse-coordinate pullback DATA. -/
theorem diagonalShearIsometry_apply (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    diagonalShearIsometry (H := H) μ ξ =
      Lp.compMeasurePreserving (Homeomorph.diagonalDifferenceShear G).symm
        (Measure.measurePreserving_diagonalDifferenceShear_symm_radonProd μ) ξ := rfl

omit [CompleteSpace H] [μ.Regular] in
/-- The inverse full L2 shear has the literal forward-coordinate pullback DATA. -/
theorem diagonalShearIsometry_symm_apply (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalShearIsometry (H := H) μ).symm ξ =
      Lp.compMeasurePreserving (Homeomorph.diagonalDifferenceShear G)
        (Measure.measurePreserving_diagonalDifferenceShear_radonProd μ) ξ := rfl

omit [CompleteSpace H] [μ.Regular] in
/-- Every actual product-L2 vector has the original inverse-shear coordinates almost everywhere. -/
theorem diagonalShearIsometry_ae_eq (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    diagonalShearIsometry (H := H) μ ξ =ᵐ[Measure.radonProd μ μ]
      fun z : G × G => ξ (z.1 * z.2, z.2) := by
  rw [diagonalShearIsometry_apply]
  filter_upwards [Lp.coeFn_compMeasurePreserving ξ
    (Measure.measurePreserving_diagonalDifferenceShear_symm_radonProd μ)] with z hz
  simpa only [Function.comp_apply, Homeomorph.diagonalDifferenceShear_symm_apply] using hz

omit [CompleteSpace H] [μ.Regular] in
/-- The actual inverse Hilbert operator has the original forward-shear coordinates a.e. -/
theorem diagonalShearIsometry_symm_ae_eq (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalShearIsometry (H := H) μ).symm ξ =ᵐ[Measure.radonProd μ μ]
      fun z : G × G => ξ (z.1 * z.2⁻¹, z.2) := by
  rw [diagonalShearIsometry_symm_apply]
  filter_upwards [Lp.coeFn_compMeasurePreserving ξ
    (Measure.measurePreserving_diagonalDifferenceShear_radonProd μ)] with z hz
  simpa only [Function.comp_apply, Homeomorph.diagonalDifferenceShear_apply] using hz

omit [CompleteSpace H] [μ.Regular] in
/-- The Hilbert operator retains the original inverse-shear compact-support vector map. -/
theorem diagonalShearIsometry_apply_compactSupport (f : C_c(G × G, H)) :
    diagonalShearIsometry (H := H) μ
      (compactSupportInclusion (Measure.radonProd μ μ) f) =
        compactSupportInclusion (Measure.radonProd μ μ)
          (CompactlySupportedContinuousMap.diagonalShearPullback f) := by
  apply Lp.ext
  let e := Homeomorph.diagonalDifferenceShear G
  have hpres := Measure.measurePreserving_diagonalDifferenceShear_symm_radonProd μ
  have hquasi : QuasiMeasurePreserving e.symm
      (Measure.radonProd μ μ) (Measure.radonProd μ μ) :=
    hpres.quasiMeasurePreserving
  have hinput := hquasi.ae_eq_comp (compactSupportInclusion_ae_eq (Measure.radonProd μ μ) f)
  filter_upwards [diagonalShearIsometry_ae_eq μ
      (compactSupportInclusion (Measure.radonProd μ μ) f), hinput,
    compactSupportInclusion_ae_eq (Measure.radonProd μ μ)
      (CompactlySupportedContinuousMap.diagonalShearPullback f)] with z h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

/-- The actual full H-valued Radon-square shear as a bounded unitary operator. -/
def diagonalShearUnitary :
    unitary (Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) :=
  Unitary.linearIsometryEquiv.symm (diagonalShearIsometry (H := H) μ)

omit [μ.Regular] in
/-- The bounded shear operator is the same literal full-L2 linear isometry. -/
@[simp]
theorem diagonalShearUnitary_coe :
    (diagonalShearUnitary (H := H) μ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
        (diagonalShearIsometry (H := H) μ).toLinearIsometry.toContinuousLinearMap :=
  rfl

omit [μ.Regular] in
/-- The actual bounded unitary retains the original inverse-shear coordinates on all vectors a.e. -/
theorem diagonalShearUnitary_ae_eq (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalShearUnitary (H := H) μ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ξ =ᵐ[Measure.radonProd μ μ]
        fun z : G × G => ξ (z.1 * z.2, z.2) :=
  diagonalShearIsometry_ae_eq μ ξ

end HaarL2

end

end MeasureTheory

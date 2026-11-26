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
# Measure-preserving shear of an abelian Haar Radon square

For a Hausdorff locally compact abelian Borel group and Haar measure `μ`, the shear
`S(s,t)=(st⁻¹,t)` and its inverse preserve `R=radonProd μ μ`.

Inverse-shear pullback gives the L² isometry `Fξ(s,t)=ξ(st,t)`, with inverse value `ξ(st⁻¹,t)`.
When the coefficient inner-product space is complete, this is a bounded unitary. No regularity
of the Haar measure, countability or s-finiteness is needed for these formulas.
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

/-- **Borel measurable structure of a Haar square.** For a topological space `G`, the square
has the measurable structure `borel(G×G)` of its product topology. -/
local instance instExactShearProductMeasurableSpace : MeasurableSpace (G × G) := borel (G × G)
local instance instExactShearProductBorelSpace : BorelSpace (G × G) := ⟨rfl⟩

namespace Measure

omit [μ.Regular] in
/-- **Difference-coordinate shear preserves the Haar Radon square.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. `Measure.map S R=R`.
Regularity of `μ` is not an extra premise. -/
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
/-- **Measure preservation of the difference-coordinate shear.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. `S : G×G → G×G` is measure
preserving for `R`. -/
theorem measurePreserving_diagonalDifferenceShear_radonProd :
    MeasurePreserving (Homeomorph.diagonalDifferenceShear G)
      (radonProd μ μ) (radonProd μ μ) :=
  ⟨(Homeomorph.diagonalDifferenceShear G).measurable,
    map_diagonalDifferenceShear_radonProd μ⟩

omit [μ.Regular] in
/-- **Measure preservation of the inverse coordinate shear.** Let `G` be a Hausdorff locally
compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. `S⁻¹(r,t)=(rt,t)` is measure
preserving for `R`. -/
theorem measurePreserving_diagonalDifferenceShear_symm_radonProd :
    MeasurePreserving (Homeomorph.diagonalDifferenceShear G).symm
      (radonProd μ μ) (radonProd μ μ) :=
  MeasurePreserving.symm (Homeomorph.diagonalDifferenceShear G).toMeasurableEquiv
    (measurePreserving_diagonalDifferenceShear_radonProd μ)

end Measure

namespace HaarL2

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Linear L² isometric equivalence by inverse-shear pullback.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. Let `H` be a complex normed
inner-product space, possibly incomplete, and `E=Lp H 2 R`. `diagonalShearIsometry μ : E
≃ₗᵢ[ℂ] E` is pullback by `S⁻¹`, with forward representative `ξ(st,t)` and inverse
representative `ξ(st⁻¹,t)`. -/
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
/-- **Forward L² shear as measure-preserving inverse pullback.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. Let `H` be a complex normed
inner-product space, possibly incomplete, and `E=Lp H 2 R`. the forward isometry sends `ξ`
to `Lp.compMeasurePreserving S⁻¹ ξ`, without a completeness assumption on `H`. -/
theorem diagonalShearIsometry_apply (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    diagonalShearIsometry (H := H) μ ξ =
      Lp.compMeasurePreserving (Homeomorph.diagonalDifferenceShear G).symm
        (Measure.measurePreserving_diagonalDifferenceShear_symm_radonProd μ) ξ := rfl

omit [CompleteSpace H] [μ.Regular] in
/-- **Inverse L² shear as forward-coordinate pullback.** Let `G` be a Hausdorff locally
compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. Let `H` be a complex normed
inner-product space, possibly incomplete, and `E=Lp H 2 R`. the inverse isometry sends `ξ`
to `Lp.compMeasurePreserving S ξ`. -/
theorem diagonalShearIsometry_symm_apply (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalShearIsometry (H := H) μ).symm ξ =
      Lp.compMeasurePreserving (Homeomorph.diagonalDifferenceShear G)
        (Measure.measurePreserving_diagonalDifferenceShear_radonProd μ) ξ := rfl

omit [CompleteSpace H] [μ.Regular] in
/-- **Almost-everywhere forward shear coordinates.** Let `G` be a Hausdorff locally compact
abelian topological group with Borel structure and Haar measure `μ`. Put `R=radonProd μ μ`
on the Borel square and `S(s,t)=(st⁻¹,t)`. Let `H` be a complex normed inner-product
space, possibly incomplete, and `E=Lp H 2 R`. for `ξ∈E`, `(diagonalShearIsometry μ
ξ)(s,t)=ξ(st,t)` for `R`-almost every `(s,t)`. -/
theorem diagonalShearIsometry_ae_eq (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    diagonalShearIsometry (H := H) μ ξ =ᵐ[Measure.radonProd μ μ]
      fun z : G × G => ξ (z.1 * z.2, z.2) := by
  rw [diagonalShearIsometry_apply]
  filter_upwards [Lp.coeFn_compMeasurePreserving ξ
    (Measure.measurePreserving_diagonalDifferenceShear_symm_radonProd μ)] with z hz
  simpa only [Function.comp_apply, Homeomorph.diagonalDifferenceShear_symm_apply] using hz

omit [CompleteSpace H] [μ.Regular] in
/-- **Almost-everywhere inverse shear coordinates.** Let `G` be a Hausdorff locally compact
abelian topological group with Borel structure and Haar measure `μ`. Put `R=radonProd μ μ`
on the Borel square and `S(s,t)=(st⁻¹,t)`. Let `H` be a complex normed inner-product
space, possibly incomplete, and `E=Lp H 2 R`. for `ξ∈E`, `((diagonalShearIsometry μ).symm
ξ)(s,t)=ξ(st⁻¹,t)` almost everywhere. -/
theorem diagonalShearIsometry_symm_ae_eq (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalShearIsometry (H := H) μ).symm ξ =ᵐ[Measure.radonProd μ μ]
      fun z : G × G => ξ (z.1 * z.2⁻¹, z.2) := by
  rw [diagonalShearIsometry_symm_apply]
  filter_upwards [Lp.coeFn_compMeasurePreserving ξ
    (Measure.measurePreserving_diagonalDifferenceShear_radonProd μ)] with z hz
  simpa only [Function.comp_apply, Homeomorph.diagonalDifferenceShear_apply] using hz

omit [CompleteSpace H] [μ.Regular] in
/-- **L² shear agrees with compact-support inverse pullback.** Let `G` be a Hausdorff locally
compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. Let `H` be a complex normed
inner-product space, possibly incomplete, and `E=Lp H 2 R`. for `f∈C_c(G×G,H)` and its
inclusion `i_R`, `diagonalShearIsometry μ (i_R f)=i_R((s,t) ↦ f(st,t))`. -/
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

/-- **Bounded Hilbert unitary of the Haar-square shear.** Let `G` be a Hausdorff locally
compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. Let `H` be a complex normed
inner-product space, possibly incomplete, and `E=Lp H 2 R`. assume `H` is complete.
`diagonalShearUnitary μ∈U(B(E))` has forward value the inverse-shear L² isometry. -/
def diagonalShearUnitary :
    unitary (Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) :=
  Unitary.linearIsometryEquiv.symm (diagonalShearIsometry (H := H) μ)

omit [μ.Regular] in
/-- **Bounded operator of the Haar-square shear unitary.** Let `G` be a Hausdorff locally
compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. Let `H` be a complex normed
inner-product space, possibly incomplete, and `E=Lp H 2 R`. assume `H` is complete. The
operator underlying `diagonalShearUnitary μ` equals the continuous linear map of
`diagonalShearIsometry μ`. -/
@[simp]
theorem diagonalShearUnitary_coe :
    (diagonalShearUnitary (H := H) μ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
        (diagonalShearIsometry (H := H) μ).toLinearIsometry.toContinuousLinearMap :=
  rfl

omit [μ.Regular] in
/-- **Almost-everywhere coordinates of the bounded shear unitary.** Let `G` be a Hausdorff
locally compact abelian topological group with Borel structure and Haar measure `μ`. Put
`R=radonProd μ μ` on the Borel square and `S(s,t)=(st⁻¹,t)`. Let `H` be a complex normed
inner-product space, possibly incomplete, and `E=Lp H 2 R`. assume `H` is complete. For
`ξ∈E`, the unitary acts almost everywhere by `(s,t) ↦ ξ(st,t)`. -/
theorem diagonalShearUnitary_ae_eq (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalShearUnitary (H := H) μ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ξ =ᵐ[Measure.radonProd μ μ]
        fun z : G × G => ξ (z.1 * z.2, z.2) :=
  diagonalShearIsometry_ae_eq μ ξ

end HaarL2

end

end MeasureTheory

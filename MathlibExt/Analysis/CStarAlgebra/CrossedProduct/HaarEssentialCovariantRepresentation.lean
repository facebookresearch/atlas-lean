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

public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.EssentialCovariantRepresentation
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarIntegratedForm
public import MathlibExt.Analysis.InnerProductSpace.EssentialRestrictionNorm
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual essential covariant pair preserves its Haar-integrated norm

The original coefficient operators have range in their actual essential
space. Integration through its linear isometric inclusion preserves every
source-vector integral. The source star identity gives the same range
property for the adjoint, so restriction preserves the original operator
norm. This provides the nondegenerate covariant norm model used by the full
source covariant norm, with no faithfulness or norm-equality assumption.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter

namespace CovariantRepresentation

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {α : PointNormCStarAction G A} (ρ : CovariantRepresentation α H)

/-- Every original integrated covariant vector lies in the actual coefficient essential space. -/
theorem haarIntegratedHom_mem_essentialSpace (f : HaarTwistedCore.Carrier μ α) (ξ : H) :
    haarIntegratedHom μ ρ f ξ ∈ ρ.algebra.essentialSpace := by
  let φ : G → ρ.algebra.essentialSpace := fun s =>
    ⟨ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ),
      ρ.algebra.range_mem_essentialSpace (f s) _⟩
  have hTransport : (∫ s : G, (φ s : H) ∂μ) =
      ρ.algebra.essentialSpace.subtypeₗᵢ (∫ s : G, φ s ∂μ) :=
    ρ.algebra.essentialSpace.subtypeₗᵢ.integral_comp_comm (μ := μ) φ
  rw [haarIntegratedHom_apply_vector]
  change (∫ s : G, (φ s : H) ∂μ) ∈ ρ.algebra.essentialSpace
  exact hTransport.symm ▸ (∫ s : G, φ s ∂μ).property

/-- The essential covariant pair retains exactly every original integrated source-vector value. -/
theorem essentialCovariantRepresentation_haarIntegratedHom_apply_coe
    (f : HaarTwistedCore.Carrier μ α) (ξ : ρ.algebra.essentialSpace) :
    (haarIntegratedHom μ ρ.essentialCovariantRepresentation f ξ : H) =
      haarIntegratedHom μ ρ f (ξ : H) := by
  let φ : G → ρ.algebra.essentialSpace := fun s =>
    ρ.essentialCovariantRepresentation.algebra (f s)
      ((ρ.essentialCovariantRepresentation.group s :
        ρ.algebra.essentialSpace →L[ℂ] ρ.algebra.essentialSpace) ξ)
  have hTransport : (∫ s : G, ρ.algebra.essentialSpace.subtypeₗᵢ (φ s) ∂μ) =
      ρ.algebra.essentialSpace.subtypeₗᵢ (∫ s : G, φ s ∂μ) :=
    ρ.algebra.essentialSpace.subtypeₗᵢ.integral_comp_comm (μ := μ) φ
  calc
    (haarIntegratedHom μ ρ.essentialCovariantRepresentation f ξ : H) =
        ρ.algebra.essentialSpace.subtypeₗᵢ (∫ s : G, φ s ∂μ) := rfl
    _ = ∫ s : G, ρ.algebra.essentialSpace.subtypeₗᵢ (φ s) ∂μ := hTransport.symm
    _ = haarIntegratedHom μ ρ f (ξ : H) := by
      rw [haarIntegratedHom_apply_vector]
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => rfl

/-- The actual essential integrated homomorphism is literal restriction of the original operator. -/
theorem essentialCovariantRepresentation_haarIntegratedHom_eq
    (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ.essentialCovariantRepresentation f =
      ((haarIntegratedHom μ ρ f).domRestrict ρ.algebra.essentialSpace).codRestrict
        ρ.algebra.essentialSpace (fun ξ => haarIntegratedHom_mem_essentialSpace μ ρ f ξ) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  exact essentialCovariantRepresentation_haarIntegratedHom_apply_coe μ ρ f ξ

/-- Actual essential restriction preserves the full original Haar-integrated operator norm. -/
theorem norm_essentialCovariantRepresentation_haarIntegratedHom
    (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ.essentialCovariantRepresentation f‖ = ‖haarIntegratedHom μ ρ f‖ := by
  have hStarRange (ξ : H) : star (haarIntegratedHom μ ρ f) ξ ∈ ρ.algebra.essentialSpace := by
    rw [← map_star]
    exact haarIntegratedHom_mem_essentialSpace μ ρ (star f) ξ
  rw [essentialCovariantRepresentation_haarIntegratedHom_eq]
  exact ContinuousLinearMap.norm_domRestrict_codRestrict_eq_of_range_star
    (haarIntegratedHom μ ρ f) ρ.algebra.essentialSpace
    (fun ξ => haarIntegratedHom_mem_essentialSpace μ ρ f ξ) hStarRange

end

end CovariantRepresentation

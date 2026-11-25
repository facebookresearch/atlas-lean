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

import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureCommutant
import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureVanishing
import MathlibExt.Analysis.InnerProductSpace.LinearPMap.ClosedGraphTransform
import MathlibExt.Analysis.InnerProductSpace.Adjoint.Restrict
import MathlibExt.MeasureTheory.Function.BoundedMeasurable.ReciprocalReCut
import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.IntegralRepresentation

/-!
# Spectral consequences of a closed graph

A closed partial linear map between complete complex Hilbert spaces has an
actual self-adjoint first graph-coordinate operator. These consumers show
that its spectral projection at zero vanishes when the partial map has dense
domain, bound the norm of a reciprocal spectral-cut integral by the inverse
cutoff, and restrict a commuting normal endomorphism to each computed
spectral range with its inherited Hilbert norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
open MathlibExt.MeasureTheory.Function
namespace ClosedGraphSpectralClient
universe uH uK
variable {H : Type uH} {K : Type uK}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The actual first graph coordinate is normal by its proved self-adjointness. -/
private theorem graphFirstNormal (A : H →ₗ.[ℂ] K) (hA : A.IsClosed) :
    IsStarNormal (LinearPMap.closedGraphFirstTransform A hA) := by
  rw [isStarNormal_iff, (LinearPMap.closedGraphFirstTransform_isSelfAdjoint A hA).star_eq]

/-- For complete complex Hilbert spaces `H` and `K`, a closed densely defined partial map
`A : H →ₗ.[ℂ] K` has zero spectral projection at zero for its actual first graph coordinate on `H`. -/
private theorem graph_zero_spectral_projection
    (A : H →ₗ.[ℂ] K) (hA : A.IsClosed) (hDense : Dense (A.domain : Set H)) :
    normalCFCPVM (LinearPMap.closedGraphFirstTransform A hA) (graphFirstNormal A hA)
      {z : spectrum ℂ (LinearPMap.closedGraphFirstTransform A hA) | (z : ℂ) = 0} = 0 := by
  exact normalCFCPVM_zero_eq_zero_of_injective
    (LinearPMap.closedGraphFirstTransform A hA) (graphFirstNormal A hA)
    (LinearPMap.closedGraphFirstTransform_injective A hA hDense)

/-- For complete complex Hilbert spaces `H` and `K`, a closed partial map `A : H →ₗ.[ℂ] K`
and positive `delta : ℝ` give an actual spectral reciprocal integral on `H` with operator norm
at most `delta⁻¹`, using the real-part cut of the first graph coordinate's own spectrum. -/
private theorem graph_reciprocal_spectral_integral_norm
    (A : H →ₗ.[ℂ] K) (hA : A.IsClosed) (delta : ℝ) (hdelta : 0 < delta) :
    ‖(normalCFCPVM (LinearPMap.closedGraphFirstTransform A hA) (graphFirstNormal A hA)).spectralIntegral
      (BoundedMeasurableFunction.reciprocalReCut
        ((↑) : spectrum ℂ (LinearPMap.closedGraphFirstTransform A hA) → ℂ)
        measurable_subtype_coe delta hdelta)‖ ≤ delta⁻¹ := by
  exact (norm_spectralIntegral_le
    (normalCFCPVM (LinearPMap.closedGraphFirstTransform A hA) (graphFirstNormal A hA))
    (BoundedMeasurableFunction.reciprocalReCut
      ((↑) : spectrum ℂ (LinearPMap.closedGraphFirstTransform A hA) → ℂ)
      measurable_subtype_coe delta hdelta)).trans
    (BoundedMeasurableFunction.norm_reciprocalReCut_le _ measurable_subtype_coe delta hdelta)

/-- The actual closed range of a computed graph spectral projection, with its inherited Hilbert norm. -/
private def spectralRange (A : H →ₗ.[ℂ] K) (hA : A.IsClosed)
    (s : Set (spectrum ℂ (LinearPMap.closedGraphFirstTransform A hA))) : ClosedSubmodule ℂ H := by
  let E := normalCFCPVM (LinearPMap.closedGraphFirstTransform A hA) (graphFirstNormal A hA)
  exact { toSubmodule := (E s).range
          isClosed' := ContinuousLinearMap.IsIdempotentElem.isClosed_range
            (E.isStarProjection s).isIdempotentElem }

/-- Completeness is supplied by the actual closed spectral range. -/
private instance spectralRangeComplete (A : H →ₗ.[ℂ] K) (hA : A.IsClosed)
    (s : Set (spectrum ℂ (LinearPMap.closedGraphFirstTransform A hA))) :
    CompleteSpace ((spectralRange A hA s).toSubmodule) :=
  (spectralRange A hA s).isClosed.isComplete.completeSpace_coe

/-- A graph-coordinate commutant preserves the actual computed spectral range. -/
private theorem spectralRange_invariant (A : H →ₗ.[ℂ] K) (hA : A.IsClosed)
    (D : H →L[ℂ] H) (hBD : Commute (LinearPMap.closedGraphFirstTransform A hA) D)
    (s : Set (spectrum ℂ (LinearPMap.closedGraphFirstTransform A hA)))
    (x : H) (hx : x ∈ spectralRange A hA s) : D x ∈ spectralRange A hA s := by
  let B := LinearPMap.closedGraphFirstTransform A hA
  let P := normalCFCPVM B (graphFirstNormal A hA) s
  have hstarBD : Commute (star B) D := by
    rw [(LinearPMap.closedGraphFirstTransform_isSelfAdjoint A hA).star_eq]
    exact hBD
  have hDP := normalCFCPVM_commute_of_commute B (graphFirstNormal A hA) D hBD hstarBD s
  change x ∈ P.range at hx
  change D x ∈ P.range
  obtain ⟨y, hy⟩ := hx
  refine ⟨D y, ?_⟩
  have hvalue := congrArg (fun T : H →L[ℂ] H => T y) hDP.eq
  change D (P y) = P (D y) at hvalue
  exact hvalue.symm.trans (congrArg D hy)

/-- Restrict the actual commutant to the computed spectral range using its earned invariance. -/
private def spectralRestriction (A : H →ₗ.[ℂ] K) (hA : A.IsClosed)
    (D : H →L[ℂ] H) (hBD : Commute (LinearPMap.closedGraphFirstTransform A hA) D)
    (s : Set (spectrum ℂ (LinearPMap.closedGraphFirstTransform A hA))) :
    spectralRange A hA s →L[ℂ] spectralRange A hA s :=
  D.restrict (p := (spectralRange A hA s).toSubmodule) (q := (spectralRange A hA s).toSubmodule)
    (fun x hx => spectralRange_invariant A hA D hBD s x hx)

/-- For complete complex Hilbert spaces `H` and `K`, a closed partial map `A : H →ₗ.[ℂ] K`
and a normal bounded endomorphism `D` commuting with its first graph coordinate yield a normal
restriction of `D` to every actual graph spectral range, with that range's inherited norm. -/
private theorem graph_spectral_normal_commutant_restriction
    (A : H →ₗ.[ℂ] K) (hA : A.IsClosed) (D : H →L[ℂ] H) (hD : IsStarNormal D)
    (hBD : Commute (LinearPMap.closedGraphFirstTransform A hA) D)
    (s : Set (spectrum ℂ (LinearPMap.closedGraphFirstTransform A hA))) :
    IsStarNormal (spectralRestriction A hA D hBD s) := by
  let : CompleteSpace ((spectralRange A hA s).toSubmodule) :=
    (spectralRange A hA s).isClosed.isComplete.completeSpace_coe
  have hAdjointCommute : Commute (LinearPMap.closedGraphFirstTransform A hA) D.adjoint := by
    have hStar : Commute (LinearPMap.closedGraphFirstTransform A hA) (star D) := by
      simpa only [(LinearPMap.closedGraphFirstTransform_isSelfAdjoint A hA).star_eq] using hBD.star_star
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hStar
  exact ContinuousLinearMap.IsStarNormal.restrict
    (p := (spectralRange A hA s).toSubmodule) hD
    (fun x hx => spectralRange_invariant A hA D hBD s x hx)
    (fun x hx => spectralRange_invariant A hA D.adjoint hAdjointCommute s x hx)

end ClosedGraphSpectralClient

end

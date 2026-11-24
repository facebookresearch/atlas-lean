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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.ConvolutionCurve
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1ToSeminormCompletion

/-!
# The literal Haar convolution integral in an actual seminorm completion

The fixed-support Banach curve is mapped through the original L1 completion
and its constructed contractive map to the same admissible seminorm's
completion. Its values are the original coefficient/group slices. The
bounded complex linear map gives both their actual integrability and the
canonical image of the original convolution as their Haar integral.

These are prerequisites of the original covariant integrated identity;
neither that identity nor the full covariant norm comparison is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)
variable (p : CStarSeminorm (Carrier μ α)) (hp : p ∈ admissibleCStarSeminorms μ α)

include hp in
/-- The literal coefficient/group curve is integrable in the same seminorm completion. -/
theorem integrable_toNonUnitalCompletion_coefficientLeft_groupLeft (f h : Carrier μ α) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
    Integrable (fun s : G =>
      p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h))) μ := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : CompleteSpace (L1Completion μ α) := l1CompletionCompleteSpace μ α
  let _ : NormedSpace ℝ (L1Completion μ α) := NormedSpace.restrictScalars ℝ ℂ _
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
  let _ : NormedSpace ℝ (BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h)) :=
    NormedSpace.restrictScalars ℝ ℂ _
  let J : BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h) →L[ℂ]
      p.NonUnitalCompletion :=
    (l1ToSeminormCompletionCLM μ α p hp).comp
      (supportedToL1Completion μ α (convolutionSupport μ α f h)
        (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h))
  have hvalues (s : G) : J (compactConvolutionCurve μ α f h s) =
      p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h)) := by
    change l1ToSeminormCompletionCLM μ α p hp
      (supportedToL1Completion μ α (convolutionSupport μ α f h)
        (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h)
        (compactConvolutionCurve μ α f h s)) = _
    rw [l1ToSeminormCompletionCLM_apply, supportedToL1Completion_apply,
      toCc_compactConvolutionCurve, fromCc_toCc, l1ToSeminormCompletion_apply]
  exact (J.integrable_comp (integrable_compactConvolutionCurve μ α f h)).congr
    (Eventually.of_forall hvalues)

include hp in
/-- The original convolution image is the Haar integral of its literal multiplier slices. -/
theorem integral_toNonUnitalCompletion_coefficientLeft_groupLeft (f h : Carrier μ α) :
    let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
    let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
    (∫ s : G, p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h)) ∂μ) =
      p.toNonUnitalCompletion (f * h) := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : CompleteSpace (L1Completion μ α) := l1CompletionCompleteSpace μ α
  let _ : NormedSpace ℝ (L1Completion μ α) := NormedSpace.restrictScalars ℝ ℂ _
  let _ : NonUnitalCStarAlgebra p.NonUnitalCompletion := p.nonUnitalCompletionCStarAlgebra
  let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
  let _ : NormedSpace ℝ (BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h)) :=
    NormedSpace.restrictScalars ℝ ℂ _
  let P : L1Completion μ α →L[ℂ] p.NonUnitalCompletion := l1ToSeminormCompletionCLM μ α p hp
  let J₀ := supportedToL1Completion μ α (convolutionSupport μ α f h)
    (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h)
  let J : BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h) →L[ℂ]
      p.NonUnitalCompletion := P.comp J₀
  have hvalues (s : G) : J (compactConvolutionCurve μ α f h s) =
      p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h)) := by
    change l1ToSeminormCompletionCLM μ α p hp
      (supportedToL1Completion μ α (convolutionSupport μ α f h)
        (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h)
        (compactConvolutionCurve μ α f h s)) = _
    rw [l1ToSeminormCompletionCLM_apply, supportedToL1Completion_apply,
      toCc_compactConvolutionCurve, fromCc_toCc, l1ToSeminormCompletion_apply]
  calc
    _ = ∫ s : G, J (compactConvolutionCurve μ α f h s) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun s => (hvalues s).symm)
    _ = J (∫ s : G, compactConvolutionCurve μ α f h s ∂μ) :=
      J.integral_comp_comm (integrable_compactConvolutionCurve μ α f h)
    _ = P (toL1Completion μ α (f * h)) := by
      change P (J₀ (∫ s : G, compactConvolutionCurve μ α f h s ∂μ)) = _
      exact congrArg P (integral_compactConvolutionCurve_toL1Completion μ α f h)
    _ = _ := l1ToSeminormCompletion_apply μ α p hp (f * h)

end

end HaarTwistedCore

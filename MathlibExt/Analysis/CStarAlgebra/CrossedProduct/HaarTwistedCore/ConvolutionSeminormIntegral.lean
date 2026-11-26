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
# Convolution as an integral in a C-star seminorm completion

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on this core satisfying p(k)≤∫ x, ‖k(x)‖ ∂μ for every core coefficient k. Write
Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for the dense coefficient
map, so ‖ιp(k)‖=p(k). For a core coefficient h and s∈G define L_s h(x)=α_s(h(s⁻¹*x)); for a∈A
define a⋅k(x)=a*k(x). For compactly supported continuous coefficients f,h, the curve
s↦ιp(f(s)⋅L_s h) is μ-integrable in Xp, and ∫ s, ιp(f(s)⋅L_s h) ∂μ=ιp(f*h).
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
/-- **Integrability of coefficient and group multiplier slices.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on this core satisfying p(k)≤∫ x, ‖k(x)‖ ∂μ for every core coefficient k. Write
Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for the dense coefficient
map, so ‖ιp(k)‖=p(k). For a core coefficient h and s∈G define L_s h(x)=α_s(h(s⁻¹*x)); for a∈A
define a⋅k(x)=a*k(x). For compactly supported continuous f,h:G→A, the Xp-valued curve
s↦ιp(f(s)⋅L_s h) is μ-integrable.
-/
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
/-- **Integral formula for convolution in a seminorm completion.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on this core satisfying p(k)≤∫ x, ‖k(x)‖ ∂μ for every core coefficient k. Write
Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for the dense coefficient
map, so ‖ιp(k)‖=p(k). For a core coefficient h and s∈G define L_s h(x)=α_s(h(s⁻¹*x)); for a∈A
define a⋅k(x)=a*k(x). For compactly supported continuous f,h:G→A, ∫ s:G, ιp(f(s)⋅L_s h)
∂μ=ιp(f*h), where (f*h)(x)=∫ s, f(s)*α_s(h(s⁻¹*x)) ∂μ.
-/
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

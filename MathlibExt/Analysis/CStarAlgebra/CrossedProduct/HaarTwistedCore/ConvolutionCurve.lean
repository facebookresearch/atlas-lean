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

public import MathlibExt.Topology.ContinuousMap.CompactlySupported.FixedSupport
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MultiplierActions
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Completion
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Literal Haar convolution as an actual fixed-support Banach-valued integral

For original f and h, the curve s ↦ f(s)·α_s(h(s⁻¹·)) lies in the stock
bounded-function subspace supported in tsupport(f)·tsupport(h). Joint
coefficient continuity makes this an actual continuous compactly supported
Banach-valued curve. Bounded point evaluations identify its integral with
the original convolution. Its bounded map to the literal L1 completion
therefore gives the original completed convolution image.

The fixed-support carrier and integral are constructed, not supplied as
model or agreement hypotheses. No raw or L1 C-star square law is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter
open scoped CompactlySupported Pointwise

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

/-- The original compact product supports both the convolution and all its coefficient slices. -/
def convolutionSupport (f h : Carrier μ α) : Set G :=
  tsupport (toCc μ α f) * tsupport (toCc μ α h)

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The product of the original two compact supports is compact. -/
theorem isCompact_convolutionSupport (f h : Carrier μ α) :
    IsCompact (convolutionSupport μ α f h) :=
  (toCc μ α f).hasCompactSupport.mul (toCc μ α h).hasCompactSupport

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The same product is closed without imposing separatedness on the original group. -/
theorem isClosed_convolutionSupport (f h : Carrier μ α) :
    IsClosed (convolutionSupport μ α f h) :=
  (isClosed_tsupport (toCc μ α h)).mul_left_of_isCompact (toCc μ α f).hasCompactSupport

/-- The literal original coefficient-left/group-left slice in one actual complete support carrier. -/
def compactConvolutionCurve (f h : Carrier μ α) (s : G) :
    BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h) := by
  let F := toCc μ α f
  let H := toCc μ α h
  let c : C_c(G, A) := coefficientLeftCc (F s) (groupLeftCc α s H)
  have hzero (x : G) (hx : x ∉ convolutionSupport μ α f h) : c x = 0 := by
    change F s * α s (H (s⁻¹ * x)) = 0
    by_cases hs : s ∈ tsupport F
    · have hH : s⁻¹ * x ∉ tsupport H := by
        intro hHx
        apply hx
        change x ∈ tsupport F * tsupport H
        simpa only [mul_inv_cancel_left] using Set.mul_mem_mul hs hHx
      rw [image_eq_zero_of_notMem_tsupport hH, α.apply_zero, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hs, zero_mul]
  have hSupport : tsupport c ⊆ convolutionSupport μ α f h := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      exact hx (hzero x hnot)
    · exact isClosed_convolutionSupport μ α f h
  exact BoundedContinuousFunction.ccToSupported ℂ A (convolutionSupport μ α f h) c hSupport

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- Every Banach-curve coefficient is the original twisted convolution kernel. -/
@[simp]
theorem compactConvolutionCurve_apply (f h : Carrier μ α) (s x : G) :
    (compactConvolutionCurve μ α f h s).1 x = f s * α s (h (s⁻¹ * x)) :=
  rfl

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The fixed-support Banach curve is exactly the existing original multiplier slice as a C_c value. -/
theorem toCc_compactConvolutionCurve (f h : Carrier μ α) (s : G) :
    BoundedContinuousFunction.supportedToCc ℂ A (convolutionSupport μ α f h)
        (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h)
        (compactConvolutionCurve μ α f h s) =
      toCc μ α (coefficientLeft μ α (f s) (groupLeft μ α s h)) := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  rfl

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- Joint original-kernel continuity gives continuity in the true fixed-support Banach norm. -/
theorem continuous_compactConvolutionCurve (f h : Carrier μ α) :
    Continuous (compactConvolutionCurve μ α f h) := by
  apply BoundedContinuousFunction.continuous_supported_of_joint ℂ A
    (convolutionSupport μ α f h) (isCompact_convolutionSupport μ α f h)
  change Continuous (fun p : G × G => kernel α (toCc μ α f) (toCc μ α h) p.2 p.1)
  exact (continuous_kernel α (toCc μ α f) (toCc μ α h)).comp continuous_swap

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The actual Banach-valued curve vanishes outside the original first compact support. -/
theorem hasCompactSupport_compactConvolutionCurve (f h : Carrier μ α) :
    HasCompactSupport (compactConvolutionCurve μ α f h) := by
  refine HasCompactSupport.intro' (toCc μ α f).hasCompactSupport (isClosed_tsupport (toCc μ α f)) ?_
  intro s hs
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  change (toCc μ α f) s * α s (h (s⁻¹ * x)) = 0
  rw [image_eq_zero_of_notMem_tsupport hs, zero_mul]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- The literal continuous compactly supported Banach curve is Haar integrable. -/
theorem integrable_compactConvolutionCurve (f h : Carrier μ α) :
    Integrable (compactConvolutionCurve μ α f h) μ :=
  (continuous_compactConvolutionCurve μ α f h).integrable_of_hasCompactSupport
    (hasCompactSupport_compactConvolutionCurve μ α f h)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- Bounded evaluation identifies the actual Banach-valued integral with the original convolution. -/
theorem toCc_integral_compactConvolutionCurve (f h : Carrier μ α) :
    let _ : NormedSpace ℝ (BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h)) :=
      NormedSpace.restrictScalars ℝ ℂ _
    BoundedContinuousFunction.supportedToCc ℂ A (convolutionSupport μ α f h)
        (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h)
        (∫ s : G, compactConvolutionCurve μ α f h s ∂μ) =
      ccConvolution μ α (toCc μ α f) (toCc μ α h) := by
  let _ : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  let _ : NormedSpace ℝ (BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h)) :=
    NormedSpace.restrictScalars ℝ ℂ _
  apply CompactlySupportedContinuousMap.ext
  intro x
  let L : BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h) →L[ℂ] A :=
    BoundedContinuousFunction.supportedEvalCLM ℂ A (convolutionSupport μ α f h) x
  have hL := L.integral_comp_comm (integrable_compactConvolutionCurve μ α f h)
  change L (∫ s : G, compactConvolutionCurve μ α f h s ∂μ) =
    ccConvolution μ α (toCc μ α f) (toCc μ α h) x
  calc
    _ = ∫ s : G, L (compactConvolutionCurve μ α f h s) ∂μ := hL.symm
    _ = ∫ s : G, f s * α s (h (s⁻¹ * x)) ∂μ := rfl
    _ = _ := (ccConvolution_apply μ α (toCc μ α f) (toCc μ α h) x).symm

/-- The original fixed-support L1 image is bounded by support measure times its sup norm. -/
theorem norm_supportedToL1_raw_le (K : Set G) (hK : IsCompact K) (hKclosed : IsClosed K)
    (b : BoundedContinuousFunction.Supported ℂ A K) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    ‖toL1Completion μ α (fromCc μ α (BoundedContinuousFunction.supportedToCc ℂ A K hK hKclosed b))‖ ≤
      μ.real K * ‖b‖ := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  have hzero (x : G) (hx : x ∉ K) : ‖b.1 x‖ = 0 := by rw [b.2 x hx, norm_zero]
  have hcompact : HasCompactSupport (fun x : G => ‖b.1 x‖) :=
    HasCompactSupport.intro' hK hKclosed hzero
  have hnorm : Integrable (fun x : G => ‖b.1 x‖) μ :=
    b.1.continuous.norm.integrable_of_hasCompactSupport hcompact
  calc
    _ = ∫ x : G, ‖b.1 x‖ ∂μ := by rw [norm_toL1Completion]; rfl
    _ = ∫ x in K, ‖b.1 x‖ ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ ∫ _ in K, ‖b‖ ∂μ :=
      integral_mono hnorm.integrableOn (integrableOn_const hK.measure_ne_top)
        (fun x => BoundedContinuousFunction.norm_coe_le_norm b.1 x)
    _ = μ.real K * ‖b‖ := by rw [setIntegral_const, smul_eq_mul]

/-- The original fixed-support functions map boundedly to their literal L1 completion images. -/
def supportedToL1Completion (K : Set G) (hK : IsCompact K) (hKclosed : IsClosed K) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    BoundedContinuousFunction.Supported ℂ A K →L[ℂ] L1Completion μ α := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let J : BoundedContinuousFunction.Supported ℂ A K →ₗ[ℂ] L1Completion μ α :=
    { toFun b :=
        toL1Completion μ α (fromCc μ α (BoundedContinuousFunction.supportedToCc ℂ A K hK hKclosed b))
      map_add' b c := by
        have heq :
            fromCc μ α (BoundedContinuousFunction.supportedToCc ℂ A K hK hKclosed (b + c)) =
              fromCc μ α (BoundedContinuousFunction.supportedToCc ℂ A K hK hKclosed b) +
                fromCc μ α (BoundedContinuousFunction.supportedToCc ℂ A K hK hKclosed c) := by
          apply ext μ α
          intro x
          rfl
        rw [heq, map_add]
      map_smul' r b := by
        have heq :
            fromCc μ α (BoundedContinuousFunction.supportedToCc ℂ A K hK hKclosed (r • b)) =
              r • fromCc μ α (BoundedContinuousFunction.supportedToCc ℂ A K hK hKclosed b) := by
          apply ext μ α
          intro x
          rfl
        rw [heq, map_smul, RingHom.id_apply] }
  exact J.mkContinuous (μ.real K) (norm_supportedToL1_raw_le μ α K hK hKclosed)

/-- The bounded fixed-support map retains the original canonical L1 coefficient image. -/
@[simp]
theorem supportedToL1Completion_apply (K : Set G) (hK : IsCompact K) (hKclosed : IsClosed K)
    (b : BoundedContinuousFunction.Supported ℂ A K) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    supportedToL1Completion μ α K hK hKclosed b =
      toL1Completion μ α (fromCc μ α (BoundedContinuousFunction.supportedToCc ℂ A K hK hKclosed b)) :=
  rfl

/-- The Banach-to-L1 map has the true finite-support-measure sup-norm bound. -/
theorem norm_supportedToL1Completion_le (K : Set G) (hK : IsCompact K) (hKclosed : IsClosed K)
    (b : BoundedContinuousFunction.Supported ℂ A K) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    ‖supportedToL1Completion μ α K hK hKclosed b‖ ≤ μ.real K * ‖b‖ :=
  norm_supportedToL1_raw_le μ α K hK hKclosed b

/-- Integrating the actual compact-support Banach curve gives the same completed convolution image. -/
theorem integral_compactConvolutionCurve_toL1Completion (f h : Carrier μ α) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NormedSpace ℝ (BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h)) :=
      NormedSpace.restrictScalars ℝ ℂ _
    supportedToL1Completion μ α (convolutionSupport μ α f h)
        (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h)
        (∫ s : G, compactConvolutionCurve μ α f h s ∂μ) = toL1Completion μ α (f * h) := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : NormedSpace ℝ (BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h)) :=
    NormedSpace.restrictScalars ℝ ℂ _
  change supportedToL1Completion μ α (convolutionSupport μ α f h)
      (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h)
      (∫ s : G, compactConvolutionCurve μ α f h s ∂μ) = toL1Completion μ α (f * h)
  rw [supportedToL1Completion_apply, toCc_integral_compactConvolutionCurve]
  rfl

/-- The original L1 integral of literal multiplier slices is the canonical Haar convolution image. -/
theorem integral_toL1Completion_coefficientLeft_groupLeft (f h : Carrier μ α) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    let _ : NormedSpace ℝ (L1Completion μ α) := NormedSpace.restrictScalars ℝ ℂ _
    (∫ s : G, toL1Completion μ α (coefficientLeft μ α (f s) (groupLeft μ α s h)) ∂μ) =
      toL1Completion μ α (f * h) := by
  let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
  let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
  let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
  let _ : CompleteSpace (L1Completion μ α) := l1CompletionCompleteSpace μ α
  let _ : NormedSpace ℝ (L1Completion μ α) := NormedSpace.restrictScalars ℝ ℂ _
  let _ : NormedSpace ℝ (BoundedContinuousFunction.Supported ℂ A (convolutionSupport μ α f h)) :=
    NormedSpace.restrictScalars ℝ ℂ _
  let J := supportedToL1Completion μ α (convolutionSupport μ α f h)
    (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h)
  have hvalues (s : G) : J (compactConvolutionCurve μ α f h s) =
      toL1Completion μ α (coefficientLeft μ α (f s) (groupLeft μ α s h)) := by
    rw [supportedToL1Completion_apply, toCc_compactConvolutionCurve, fromCc_toCc]
  calc
    _ = ∫ s : G, J (compactConvolutionCurve μ α f h s) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun s => (hvalues s).symm)
    _ = J (∫ s : G, compactConvolutionCurve μ α f h s ∂μ) :=
      J.integral_comp_comm (integrable_compactConvolutionCurve μ α f h)
    _ = _ := integral_compactConvolutionCurve_toL1Completion μ α f h

end

end HaarTwistedCore

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
# Twisted convolution as a Banach-valued Haar integral

Let G be a topological group with a measurable structure, μ any measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For compactly supported continuous
coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)). Write
E_K={b∈C_b(G,A):b(x)=0 for x∉K}, with its supremum norm. Each Fₛ belongs to this Banach space.
The curve s↦Fₛ is norm-continuous and compactly supported. If G has its Borel measurable
structure and μ is left Haar, its Bochner integral has coefficient function f*h. For locally
compact Borel G and regular left Haar μ, let X₁ be the L¹ norm completion of the twisted
coefficient core with dense map ι₁. For b∈E_K let c_b be its compactly supported coefficient
function and J_K(b)=ι₁(c_b). This bounded complex linear map satisfies ‖J_K(b)‖≤μ.real(K)‖b‖∞
and commutes with the convolution integral.
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

/-- **Product support for twisted convolution.**

Let G be a topological group with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action. For compactly supported continuous f,h:G→A,
convolutionSupport μ α f h is K=tsupport(f)*tsupport(h), where tsupport is the closure of the
nonzero set.
-/
def convolutionSupport (f h : Carrier μ α) : Set G :=
  tsupport (toCc μ α f) * tsupport (toCc μ α h)

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- **Compactness of the convolution support.**

Let G be a topological group with a measurable structure, μ any measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For compactly supported continuous
f,h:G→A, K=convolutionSupport μ α f h=tsupport(f)*tsupport(h) is compact.
-/
theorem isCompact_convolutionSupport (f h : Carrier μ α) :
    IsCompact (convolutionSupport μ α f h) :=
  (toCc μ α f).hasCompactSupport.mul (toCc μ α h).hasCompactSupport

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- **Closedness of the convolution support.**

Let G be a topological group with a measurable structure, μ any measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For compactly supported continuous
f,h:G→A, K=convolutionSupport μ α f h=tsupport(f)*tsupport(h) is closed.
-/
theorem isClosed_convolutionSupport (f h : Carrier μ α) :
    IsClosed (convolutionSupport μ α f h) :=
  (isClosed_tsupport (toCc μ α h)).mul_left_of_isCompact (toCc μ α f).hasCompactSupport

/-- **Convolution kernel in the fixed-support Banach space.**

Let G be a topological group with a measurable structure, μ any measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For compactly supported continuous
coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)). Write
E_K={b∈C_b(G,A):b(x)=0 for x∉K}, with its supremum norm. Each Fₛ belongs to this Banach space.
For s∈G, compactConvolutionCurve μ α f h s is Fₛ.
-/
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
/-- **Evaluation of the convolution kernel.**

Let G be a topological group with a measurable structure, μ any measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For compactly supported continuous
coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)). Write
E_K={b∈C_b(G,A):b(x)=0 for x∉K}, with its supremum norm. Each Fₛ belongs to this Banach space.
For s,x∈G, (compactConvolutionCurve μ α f h s)(x)=f(s)*αₛ(h(s⁻¹*x)).
-/
@[simp]
theorem compactConvolutionCurve_apply (f h : Carrier μ α) (s x : G) :
    (compactConvolutionCurve μ α f h s).1 x = f s * α s (h (s⁻¹ * x)) :=
  rfl

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- **The convolution kernel as a compactly supported coefficient.**

Let G be a topological group with a measurable structure, μ any measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For compactly supported continuous
coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)). Write
E_K={b∈C_b(G,A):b(x)=0 for x∉K}, with its supremum norm. Each Fₛ belongs to this Banach space.
Let c_K:E_K→C_c(G,A) take the underlying compactly supported coefficient function. Then
c_K(Fₛ)=coefficientLeft(f(s))(groupLeft(s,h)), whose value at x is f(s)*αₛ(h(s⁻¹*x));
groupLeft(s,h)(x)=αₛ(h(s⁻¹*x)) and coefficientLeft(a)(k)(x)=a*k(x).
-/
theorem toCc_compactConvolutionCurve (f h : Carrier μ α) (s : G) :
    BoundedContinuousFunction.supportedToCc ℂ A (convolutionSupport μ α f h)
        (isCompact_convolutionSupport μ α f h) (isClosed_convolutionSupport μ α f h)
        (compactConvolutionCurve μ α f h s) =
      toCc μ α (coefficientLeft μ α (f s) (groupLeft μ α s h)) := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  rfl

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- **Supremum-norm continuity of the convolution curve.**

Let G be a topological group with a measurable structure, μ any measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For compactly supported continuous
coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)). Write
E_K={b∈C_b(G,A):b(x)=0 for x∉K}, with its supremum norm. Each Fₛ belongs to this Banach space.
The map s↦compactConvolutionCurve μ α f h s=Fₛ is continuous from G to the supremum-norm
topology of E_K.
-/
theorem continuous_compactConvolutionCurve (f h : Carrier μ α) :
    Continuous (compactConvolutionCurve μ α f h) := by
  apply BoundedContinuousFunction.continuous_supported_of_joint ℂ A
    (convolutionSupport μ α f h) (isCompact_convolutionSupport μ α f h)
  change Continuous (fun p : G × G => kernel α (toCc μ α f) (toCc μ α h) p.2 p.1)
  exact (continuous_kernel α (toCc μ α f) (toCc μ α h)).comp continuous_swap

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- **Compact support in the integration variable.**

Let G be a topological group with a measurable structure, μ any measure on G, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For compactly supported continuous
coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)). Write
E_K={b∈C_b(G,A):b(x)=0 for x∉K}, with its supremum norm. Each Fₛ belongs to this Banach space.
The curve s↦Fₛ is zero outside tsupport(f), so compactConvolutionCurve μ α f h has compact
support in s.
-/
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
/-- **Bochner integrability of the convolution curve.**

Let G be a topological group with its Borel measurable structure, μ a left Haar measure on G,
A a nonunital complex C-star algebra and α a point-norm action of G on A. For compactly
supported continuous coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and
Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)). Write E_K={b∈C_b(G,A):b(x)=0 for x∉K}, with its supremum norm. Each
Fₛ belongs to this Banach space. The E_K-valued curve s↦compactConvolutionCurve μ α f h s=Fₛ
is Bochner integrable with respect to μ.
-/
theorem integrable_compactConvolutionCurve (f h : Carrier μ α) :
    Integrable (compactConvolutionCurve μ α f h) μ :=
  (continuous_compactConvolutionCurve μ α f h).integrable_of_hasCompactSupport
    (hasCompactSupport_compactConvolutionCurve μ α f h)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **The Banach-valued integral equals twisted convolution.**

Let G be a topological group with its Borel measurable structure, μ a left Haar measure on G,
A a nonunital complex C-star algebra, and α a point-norm action of G on A. For compactly
supported continuous coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and define
Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)).

View s↦Fₛ as a curve in the Banach space of bounded continuous A-valued functions supported in
K, with the supremum norm. The compactly supported continuous function underlying its integral
∫ s, Fₛ ∂μ equals the twisted convolution f*h. For every x∈G, `(∫ s, Fₛ ∂μ)(x) = ∫ s,
f(s)*αₛ(h(s⁻¹*x)) ∂μ = (f*h)(x)`.
-/
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

/-- **L¹ bound for functions supported in a compact set.**

Let G be a locally compact topological group with its Borel measurable structure, μ a regular
left Haar measure, A a nonunital complex C-star algebra and α a point-norm action of G on A.
Let X₁=L1Completion μ α be the L¹ norm completion of the compactly supported twisted
coefficient core, with ‖k‖₁=∫ x, ‖k(x)‖ ∂μ and dense coefficient map ι₁. For a compact closed
K⊆G, let E_K be the supremum-norm Banach space of bounded continuous A-valued functions
vanishing outside K. For b∈E_K, c_b is its compactly supported coefficient function, and
J_K(b)=ι₁(c_b). The coefficient class satisfies ‖ι₁(c_b)‖≤μ.real(K)‖b‖∞, where μ.real(K) is
the finite real measure of K.
-/
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

/-- **Bounded inclusion of fixed-support functions in the L¹ completion.**

Let G be a locally compact topological group with its Borel measurable structure, μ a regular
left Haar measure, A a nonunital complex C-star algebra and α a point-norm action of G on A.
Let X₁=L1Completion μ α be the L¹ norm completion of the compactly supported twisted
coefficient core, with ‖k‖₁=∫ x, ‖k(x)‖ ∂μ and dense coefficient map ι₁. For a compact closed
K⊆G, let E_K be the supremum-norm Banach space of bounded continuous A-valued functions
vanishing outside K. For b∈E_K, c_b is its compactly supported coefficient function, and
J_K(b)=ι₁(c_b). The complex linear map supportedToL1Completion μ α K:E_K→X₁ is J_K, with
operator norm at most μ.real(K).
-/
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

/-- **Value of the fixed-support L¹ inclusion.**

Let G be a locally compact topological group with its Borel measurable structure, μ a regular
left Haar measure, A a nonunital complex C-star algebra and α a point-norm action of G on A.
Let X₁=L1Completion μ α be the L¹ norm completion of the compactly supported twisted
coefficient core, with ‖k‖₁=∫ x, ‖k(x)‖ ∂μ and dense coefficient map ι₁. For a compact closed
K⊆G, let E_K be the supremum-norm Banach space of bounded continuous A-valued functions
vanishing outside K. For b∈E_K, c_b is its compactly supported coefficient function, and
J_K(b)=ι₁(c_b). For b∈E_K, supportedToL1Completion μ α K b=J_K(b)=ι₁(c_b).
-/
@[simp]
theorem supportedToL1Completion_apply (K : Set G) (hK : IsCompact K) (hKclosed : IsClosed K)
    (b : BoundedContinuousFunction.Supported ℂ A K) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    supportedToL1Completion μ α K hK hKclosed b =
      toL1Completion μ α (fromCc μ α (BoundedContinuousFunction.supportedToCc ℂ A K hK hKclosed b)) :=
  rfl

/-- **Norm bound for the fixed-support L¹ inclusion.**

Let G be a locally compact topological group with its Borel measurable structure, μ a regular
left Haar measure, A a nonunital complex C-star algebra and α a point-norm action of G on A.
Let X₁=L1Completion μ α be the L¹ norm completion of the compactly supported twisted
coefficient core, with ‖k‖₁=∫ x, ‖k(x)‖ ∂μ and dense coefficient map ι₁. For a compact closed
K⊆G, let E_K be the supremum-norm Banach space of bounded continuous A-valued functions
vanishing outside K. For b∈E_K, c_b is its compactly supported coefficient function, and
J_K(b)=ι₁(c_b). For b∈E_K, ‖supportedToL1Completion μ α K b‖=‖J_K(b)‖≤μ.real(K)‖b‖∞.
-/
theorem norm_supportedToL1Completion_le (K : Set G) (hK : IsCompact K) (hKclosed : IsClosed K)
    (b : BoundedContinuousFunction.Supported ℂ A K) :
    let _ : NonUnitalNormedRing (L1Completion μ α) := l1CompletionNonUnitalNormedRing μ α
    let _ : NormedSpace ℂ (L1Completion μ α) := l1CompletionNormedSpace μ α
    let _ : StarRing (L1Completion μ α) := l1CompletionStarRing μ α
    ‖supportedToL1Completion μ α K hK hKclosed b‖ ≤ μ.real K * ‖b‖ :=
  norm_supportedToL1_raw_le μ α K hK hKclosed b

/-- **Convolution integral commutes with the L¹ inclusion.**

Let G be a locally compact topological group with its Borel measurable structure, μ a regular
left Haar measure, A a nonunital complex C-star algebra and α a point-norm action of G on A.
For compactly supported continuous coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and
Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)). Write E_K={b∈C_b(G,A):b(x)=0 for x∉K}, with its supremum norm. Each
Fₛ belongs to this Banach space. Let X₁=L1Completion μ α be the L¹ norm completion of the
compactly supported twisted coefficient core, with ‖k‖₁=∫ x, ‖k(x)‖ ∂μ and dense coefficient
map ι₁. Let J_K:E_K→X₁ send b to ι₁(c_b), the class of its underlying compactly supported
coefficient. Then J_K(∫ s, Fₛ ∂μ)=ι₁(f*h), where (f*h)(x)=∫ s, f(s)*αₛ(h(s⁻¹*x)) ∂μ.
-/
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

/-- **Integrated coefficient-translation slices give L¹ convolution.**

Let G be a locally compact topological group with its Borel measurable structure, μ a regular
left Haar measure, A a nonunital complex C-star algebra and α a point-norm action of G on A.
For compactly supported continuous coefficients f,h:G→A, put K=tsupport(f)*tsupport(h) and
Fₛ(x)=f(s)*αₛ(h(s⁻¹*x)). Let X₁=L1Completion μ α be the L¹ norm completion of the compactly
supported twisted coefficient core, with ‖k‖₁=∫ x, ‖k(x)‖ ∂μ and dense coefficient map ι₁. The
compact coefficient Fₛ is coefficientLeft(f(s))(groupLeft(s,h)), with
groupLeft(s,h)(x)=αₛ(h(s⁻¹*x)) and coefficientLeft(a)(k)(x)=a*k(x). In the Banach space X₁, ∫
s, ι₁(Fₛ) ∂μ=ι₁(f*h).
-/
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

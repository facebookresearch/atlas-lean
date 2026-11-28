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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Haar twisted convolution of compact coefficients

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h, write (f*h)(s)=∫ t:G, f(t)*α_t(h(t⁻¹*s)) ∂μ. The convolution is continuous and compactly
supported, with tsupport(f*h)⊆tsupport(f)*tsupport(h). It is associative and complex-bilinear
on the coefficient core, with zero coefficient as an absorbing element.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped CompactlySupported Topology Pointwise

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- **Kernel of twisted convolution.**

Let G be a group with a topology, A a nonunital complex C-star algebra and α a point-norm
action. For compactly supported continuous f,h:G→A, define K(s,t)=f(t)*α_t(h(t⁻¹*s)). The
function kernel α f h s t is K(s,t).
-/
def kernel (α : PointNormCStarAction G A) (f g : C_c(G, A)) (s t : G) : A :=
  f t * α t (g (t⁻¹ * s))

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **Joint continuity of the convolution kernel.**

Let G be a topological group, A a nonunital complex C-star algebra and α a point-norm action.
For compactly supported continuous f,h:G→A, define K(s,t)=f(t)*α_t(h(t⁻¹*s)). The map
(s,t)↦K(s,t) from G×G to A is continuous.
-/
theorem continuous_kernel (α : PointNormCStarAction G A) (f g : C_c(G, A)) :
    Continuous (Function.uncurry (kernel α f g)) := by
  exact ((map_continuous f).comp continuous_snd).mul
    (α.continuous_apply continuous_snd
      ((map_continuous g).comp (continuous_snd.inv.mul continuous_fst)))

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **The kernel vanishes outside the first coefficient support.**

Let G be a group with a topology, A a nonunital complex C-star algebra and α a point-norm
action. For compactly supported continuous f,h:G→A, define K(s,t)=f(t)*α_t(h(t⁻¹*s)). If
t∉tsupport(f), then K(s,t)=0 for every s∈G; tsupport denotes the closure of the nonzero set.
-/
theorem kernel_zero_of_notMem_tsupport_left (α : PointNormCStarAction G A)
    (f g : C_c(G, A)) (s t : G) (ht : t ∉ tsupport f) : kernel α f g s t = 0 := by
  rw [kernel, image_eq_zero_of_notMem_tsupport ht, zero_mul]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Integrability of each convolution kernel.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For compactly supported continuous f,h:G→A,
define K(s,t)=f(t)*α_t(h(t⁻¹*s)). For every s∈G, t↦K(s,t) is μ-integrable.
-/
theorem integrable_kernel (α : PointNormCStarAction G A) (f g : C_c(G, A)) (s : G) :
    Integrable (kernel α f g s) μ := by
  have hc : Continuous (kernel α f g s) :=
    (continuous_kernel α f g).comp (continuous_const.prodMk continuous_id)
  have hcomp : HasCompactSupport (kernel α f g s) :=
    HasCompactSupport.intro' f.hasCompactSupport (isClosed_tsupport f)
      (kernel_zero_of_notMem_tsupport_left α f g s)
  exact hc.integrable_of_hasCompactSupport hcomp

/-- **Coefficient value of twisted convolution.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For compactly supported
continuous f,h:G→A, define K(s,t)=f(t)*α_t(h(t⁻¹*s)). The value convolutionValue μ α f h s is
∫ t:G, K(s,t) ∂μ.
-/
def convolutionValue (α : PointNormCStarAction G A) (f g : C_c(G, A)) (s : G) : A :=
  letI : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  ∫ t : G, kernel α f g s t ∂μ

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [μ.IsHaarMeasure] [μ.Regular] in
/-- **Convolution vanishes outside the product of supports.**

Let G be a group with a topology and measurable structure, μ any measure on G, A a nonunital
complex C-star algebra and α a point-norm action. For compactly supported continuous f,h:G→A,
define K(s,t)=f(t)*α_t(h(t⁻¹*s)). If s∉tsupport(f)*tsupport(h), then convolutionValue μ α f h
s=∫ t, K(s,t) ∂μ=0.
-/
theorem convolutionValue_zero_of_notMem_product (α : PointNormCStarAction G A)
    (f g : C_c(G, A)) (s : G) (hs : s ∉ tsupport f * tsupport g) :
    convolutionValue μ α f g s = 0 := by
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun t => by
    change kernel α f g s t = 0
    by_cases ht : t ∈ tsupport f
    · have hg : t⁻¹ * s ∉ tsupport g := by
        intro hgt
        apply hs
        simpa only [mul_inv_cancel_left] using Set.mul_mem_mul ht hgt
      rw [kernel, image_eq_zero_of_notMem_tsupport hg, α.apply_zero, mul_zero]
    · exact kernel_zero_of_notMem_tsupport_left α f g s t ht

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Continuity of the convolution coefficient.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For compactly supported continuous f,h:G→A,
define K(s,t)=f(t)*α_t(h(t⁻¹*s)). The coefficient function s↦∫ t:G, K(s,t) ∂μ is continuous.
-/
theorem continuous_convolutionValue (α : PointNormCStarAction G A) (f g : C_c(G, A)) :
    Continuous (convolutionValue μ α f g) := by
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  let L : ℂ →L[ℂ] A →L[ℂ] A := ContinuousLinearMap.lsmul ℂ ℂ
  have hq : IntegrableOn (fun _ : G => (1 : ℂ)) (tsupport f) μ :=
    integrableOn_const f.hasCompactSupport.measure_ne_top
  have hc :=
    _root_.continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
      L f.hasCompactSupport (continuous_kernel α f g).continuousOn
      (fun s t _ ht => kernel_zero_of_notMem_tsupport_left α f g s t ht) hq
      (s := Set.univ)
  have hfun : (fun s : G => ∫ t : G, L (1 : ℂ) (kernel α f g s t) ∂μ) =
      convolutionValue μ α f g := by
    funext s
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only [L]
      rw [ContinuousLinearMap.lsmul_apply, one_smul]
  rw [hfun] at hc
  exact continuousOn_univ.mp hc

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- **Support bound for twisted convolution.**

Let G be a topological group with a measurable structure, μ a measure on G, A a nonunital
complex C-star algebra and α a point-norm action. For compactly supported continuous f,h:G→A,
define K(s,t)=f(t)*α_t(h(t⁻¹*s)). For v(s)=∫ t, K(s,t) ∂μ,
tsupport(v)⊆tsupport(f)*tsupport(h).
-/
theorem tsupport_convolutionValue_subset (α : PointNormCStarAction G A) (f g : C_c(G, A)) :
    tsupport (convolutionValue μ α f g) ⊆ tsupport f * tsupport g := by
  apply closure_minimal
  · intro s hs
    by_contra hnot
    exact hs (convolutionValue_zero_of_notMem_product μ α f g s hnot)
  · exact (isClosed_tsupport g).mul_left_of_isCompact f.hasCompactSupport

/-- **Compactly supported continuous convolution.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For f,h∈C_c(G,A),
ccConvolution μ α f h is the compactly supported continuous function s↦∫ t:G,
f(t)*α_t(h(t⁻¹*s)) ∂μ.
-/
def ccConvolution (α : PointNormCStarAction G A) (f g : C_c(G, A)) : C_c(G, A) where
  toFun := convolutionValue μ α f g
  continuous_toFun := continuous_convolutionValue μ α f g
  hasCompactSupport' :=
    (f.hasCompactSupport.mul g.hasCompactSupport).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_convolutionValue_subset μ α f g)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Evaluation of compactly supported convolution.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For f,h∈C_c(G,A) and s∈G, ccConvolution μ α f h
s=∫ t:G, f(t)*α_t(h(t⁻¹*s)) ∂μ.
-/
theorem ccConvolution_apply (α : PointNormCStarAction G A) (f g : C_c(G, A)) (s : G) :
    ccConvolution μ α f g s =
      letI : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
      ∫ t : G, f t * α t (g (t⁻¹ * s)) ∂μ :=
  rfl

/-- **Convolution on the measure-indexed coefficient core.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h, write (f*h)(s)=∫ t:G, f(t)*α_t(h(t⁻¹*s)) ∂μ. The map convolution μ α sends f,h∈Carrier μ
α to the core element f*h with these compactly supported continuous coefficient values.
-/
def convolution (α : PointNormCStarAction G A) (f g : Carrier μ α) : Carrier μ α :=
  fromCc μ α (ccConvolution μ α (toCc μ α f) (toCc μ α g))

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Evaluation of a core convolution.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For f,h∈Carrier μ α and s∈G, convolution μ α f h
s=∫ t:G, f(t)*α_t(h(t⁻¹*s)) ∂μ.
-/
theorem convolution_apply (α : PointNormCStarAction G A) (f g : Carrier μ α) (s : G) :
    convolution μ α f g s =
      letI : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
      ∫ t : G, f t * α t (g (t⁻¹ * s)) ∂μ :=
  rfl

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Zero in the first convolution factor.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f,h, write (f*h)(s)=∫ t:G,
f(t)*α_t(h(t⁻¹*s)) ∂μ. For every h∈Carrier μ α, convolution μ α 0 h=0.
-/
theorem convolution_zero_left (α : PointNormCStarAction G A) (g : Carrier μ α) :
    convolution μ α 0 g = 0 := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [convolution_apply]
  simp only [toCc_zero, CompactlySupportedContinuousMap.zero_apply, zero_mul, integral_zero]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Zero in the second convolution factor.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f,h, write (f*h)(s)=∫ t:G,
f(t)*α_t(h(t⁻¹*s)) ∂μ. For every f∈Carrier μ α, convolution μ α f 0=0.
-/
theorem convolution_zero_right (α : PointNormCStarAction G A) (f : Carrier μ α) :
    convolution μ α f 0 = 0 := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [convolution_apply]
  simp only [toCc_zero, CompactlySupportedContinuousMap.zero_apply,
    α.apply_zero, mul_zero, integral_zero]

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Additivity in the first convolution factor.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f,h, write (f*h)(s)=∫ t:G,
f(t)*α_t(h(t⁻¹*s)) ∂μ. For f,h,k∈Carrier μ α, (f+h)*k=f*k+h*k.
-/
theorem convolution_add_left (α : PointNormCStarAction G A) (f g h : Carrier μ α) :
    convolution μ α (f + g) h = convolution μ α f h + convolution μ α g h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [toCc_add, CompactlySupportedContinuousMap.add_apply]
  rw [convolution_apply, convolution_apply, convolution_apply]
  have hk : (fun t : G => (f + g) t * α t (h (t⁻¹ * s))) =
      (fun t : G => f t * α t (h (t⁻¹ * s)) + g t * α t (h (t⁻¹ * s))) := by
    funext t
    rw [toCc_add, CompactlySupportedContinuousMap.add_apply, add_mul]
  rw [hk]
  exact integral_add (integrable_kernel μ α (toCc μ α f) (toCc μ α h) s)
    (integrable_kernel μ α (toCc μ α g) (toCc μ α h) s)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Additivity in the second convolution factor.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f,h, write (f*h)(s)=∫ t:G,
f(t)*α_t(h(t⁻¹*s)) ∂μ. For f,h,k∈Carrier μ α, f*(h+k)=f*h+f*k.
-/
theorem convolution_add_right (α : PointNormCStarAction G A) (f g h : Carrier μ α) :
    convolution μ α f (g + h) = convolution μ α f g + convolution μ α f h := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [toCc_add, CompactlySupportedContinuousMap.add_apply]
  rw [convolution_apply, convolution_apply, convolution_apply]
  have hk : (fun t : G => f t * α t ((g + h) (t⁻¹ * s))) =
      (fun t : G => f t * α t (g (t⁻¹ * s)) + f t * α t (h (t⁻¹ * s))) := by
    funext t
    rw [toCc_add, CompactlySupportedContinuousMap.add_apply, α.apply_add, mul_add]
  rw [hk]
  exact integral_add (integrable_kernel μ α (toCc μ α f) (toCc μ α g) s)
    (integrable_kernel μ α (toCc μ α f) (toCc μ α h) s)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Complex scaling in the first convolution factor.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f,h, write (f*h)(s)=∫ t:G,
f(t)*α_t(h(t⁻¹*s)) ∂μ. For c∈ℂ and f,h∈Carrier μ α, (c•f)*h=c•(f*h).
-/
theorem convolution_smul_left (α : PointNormCStarAction G A) (c : ℂ) (f g : Carrier μ α) :
    convolution μ α (c • f) g = c • convolution μ α f g := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [toCc_smul, CompactlySupportedContinuousMap.smul_apply]
  rw [convolution_apply, convolution_apply]
  let L : A →L[ℂ] A := c • ContinuousLinearMap.id ℂ A
  have hL (z : A) : L z = c • z := rfl
  have hk : (fun t : G => (c • f) t * α t (g (t⁻¹ * s))) =
      (fun t : G => L (f t * α t (g (t⁻¹ * s)))) := by
    funext t
    rw [toCc_smul, CompactlySupportedContinuousMap.smul_apply, hL]
    exact smul_mul_assoc _ _ _
  rw [hk]
  simpa only [hL, kernel] using
    L.integral_comp_comm (integrable_kernel μ α (toCc μ α f) (toCc μ α g) s)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Complex scaling in the second convolution factor.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f,h, write (f*h)(s)=∫ t:G,
f(t)*α_t(h(t⁻¹*s)) ∂μ. For c∈ℂ and f,h∈Carrier μ α, f*(c•h)=c•(f*h).
-/
theorem convolution_smul_right (α : PointNormCStarAction G A) (c : ℂ) (f g : Carrier μ α) :
    convolution μ α f (c • g) = c • convolution μ α f g := by
  apply ext μ α
  intro s
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  rw [toCc_smul, CompactlySupportedContinuousMap.smul_apply]
  rw [convolution_apply, convolution_apply]
  let L : A →L[ℂ] A := c • ContinuousLinearMap.id ℂ A
  have hL (z : A) : L z = c • z := rfl
  have hk : (fun t : G => f t * α t ((c • g) (t⁻¹ * s))) =
      (fun t : G => L (f t * α t (g (t⁻¹ * s)))) := by
    funext t
    rw [toCc_smul, CompactlySupportedContinuousMap.smul_apply, α.apply_smul, mul_smul_comm, hL]
  rw [hk]
  simpa only [hL, kernel] using
    L.integral_comp_comm (integrable_kernel μ α (toCc μ α f) (toCc μ α g) s)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Associativity at each convolution coefficient.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f,h, write (f*h)(s)=∫ t:G,
f(t)*α_t(h(t⁻¹*s)) ∂μ. For f,h,k∈C_c(G,A) and s∈G, convolutionValue μ α (ccConvolution μ α f
h) k s=convolutionValue μ α f (ccConvolution μ α h k) s.
-/
theorem convolutionValue_assoc (α : PointNormCStarAction G A) (f g h : C_c(G, A)) (s : G) :
    convolutionValue μ α (ccConvolution μ α f g) h s =
      convolutionValue μ α f (ccConvolution μ α g h) s := by
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  let K : G → G → A := fun t r => kernel α f g t r * α t (h (t⁻¹ * s))
  have hKcont : Continuous K.uncurry :=
    (continuous_kernel α f g).mul
      (α.continuous_apply continuous_fst
        ((map_continuous h).comp (continuous_fst.inv.mul_const s)))
  let Sfg : Set G := tsupport f * tsupport g
  have hSfgcompact : IsCompact Sfg := f.hasCompactSupport.mul g.hasCompactSupport
  have hSfgclosed : IsClosed Sfg :=
    (isClosed_tsupport g).mul_left_of_isCompact f.hasCompactSupport
  have hKzero (p : G × G) (hp : p ∉ Sfg ×ˢ tsupport f) : K p.1 p.2 = 0 := by
    by_cases hr : p.2 ∈ tsupport f
    · have ht : p.1 ∉ Sfg := fun ht => hp ⟨ht, hr⟩
      have hg : p.2⁻¹ * p.1 ∉ tsupport g := by
        intro hgp
        apply ht
        simpa only [mul_inv_cancel_left] using Set.mul_mem_mul hr hgp
      simp only [K, kernel, image_eq_zero_of_notMem_tsupport hg, α.apply_zero, mul_zero, zero_mul]
    · simp only [K, kernel_zero_of_notMem_tsupport_left α f g p.1 p.2 hr, zero_mul]
  have hKcompact : HasCompactSupport K.uncurry :=
    HasCompactSupport.intro' (hSfgcompact.prod f.hasCompactSupport)
      (hSfgclosed.prod (isClosed_tsupport f)) hKzero
  have hLeft : convolutionValue μ α (ccConvolution μ α f g) h s =
      ∫ t : G, (∫ r : G, K t r ∂μ) ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      let R : A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A).flip (α t (h (t⁻¹ * s)))
      have hR := R.integral_comp_comm (integrable_kernel μ α f g t)
      rw [kernel, ccConvolution_apply]
      simpa only [K, kernel, R,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using hR.symm
  have hSwap : (∫ t : G, (∫ r : G, K t r ∂μ) ∂μ) =
      ∫ r : G, (∫ t : G, K t r ∂μ) ∂μ :=
    MeasureTheory.integral_integral_swap_of_hasCompactSupport
      hKcont hKcompact
  have hRight : (∫ r : G, (∫ t : G, K t r ∂μ) ∂μ) =
      convolutionValue μ α f (ccConvolution μ α g h) s := by
    apply integral_congr_ae
    exact Eventually.of_forall fun r => by
      let a : A →L[ℂ] A :=
        ⟨LinearMap.ofClass (α.aut r), (StarAlgEquiv.isometry (α.aut r)).continuous⟩
      let L : A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A (f r)).comp a
      have hL (z : A) : L z = f r * α r z := rfl
      have hPoint (u : G) : K (r * u) r = L (kernel α g h (r⁻¹ * s) u) := by
        calc
          K (r * u) r = (f r * α r (g u)) *
              α r (α u (h (u⁻¹ * (r⁻¹ * s)))) := by
            simp only [K, kernel, inv_mul_cancel_left, mul_inv_rev, mul_assoc, α.apply_mul]
          _ = f r * (α r (g u) * α r (α u (h (u⁻¹ * (r⁻¹ * s))))) :=
            mul_assoc _ _ _
          _ = f r * α r (g u * α u (h (u⁻¹ * (r⁻¹ * s)))) :=
            congrArg (fun z : A => f r * z) (α.apply_mul_elem r _ _).symm
          _ = L (kernel α g h (r⁻¹ * s) u) := (hL _).symm
      calc
        (∫ t : G, K t r ∂μ) = ∫ u : G, K (r * u) r ∂μ :=
          (integral_mul_left_eq_self (μ := μ) (fun t : G => K t r) r).symm
        _ = ∫ u : G, L (kernel α g h (r⁻¹ * s) u) ∂μ :=
          integral_congr_ae (Eventually.of_forall hPoint)
        _ = L (∫ u : G, kernel α g h (r⁻¹ * s) u ∂μ) :=
          L.integral_comp_comm (integrable_kernel μ α g h (r⁻¹ * s))
        _ = kernel α f (ccConvolution μ α g h) s r := by
          rw [hL]
          rfl
  exact hLeft.trans (hSwap.trans hRight)

omit [LocallyCompactSpace G] [μ.Regular] in
/-- **Associativity of Haar twisted convolution.**

Let G be a Borel topological group with left Haar measure μ, A a nonunital complex C-star
algebra and α a point-norm action of G on A. For core coefficients f,h, write (f*h)(s)=∫ t:G,
f(t)*α_t(h(t⁻¹*s)) ∂μ. For all f,h,k∈Carrier μ α, (f*h)*k=f*(h*k).
-/
theorem convolution_assoc (α : PointNormCStarAction G A) (f g h : Carrier μ α) :
    convolution μ α (convolution μ α f g) h = convolution μ α f (convolution μ α g h) := by
  apply ext μ α
  intro s
  change convolutionValue μ α
      (ccConvolution μ α (toCc μ α f) (toCc μ α g)) (toCc μ α h) s =
    convolutionValue μ α (toCc μ α f)
      (ccConvolution μ α (toCc μ α g) (toCc μ α h)) s
  exact convolutionValue_assoc μ α (toCc μ α f) (toCc μ α g) (toCc μ α h) s

end

end HaarTwistedCore

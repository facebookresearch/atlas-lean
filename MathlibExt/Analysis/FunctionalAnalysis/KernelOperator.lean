/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-!
# Integral operators with a continuous kernel on `C([0, 1], ℝ)`

For a continuous kernel `k : [0, 1] × [0, 1] → ℝ`, the integral operator
`(K f) (x) = ∫₀¹ k (x, y) f (y) dy` is a bounded operator on `C([0, 1], ℝ)`
with `‖K‖ ≤ ‖k‖∞`, and it is compact: the image of the unit ball is
equicontinuous by uniform continuity of `k`, so Arzelà–Ascoli applies.
A separable kernel `k (x, y) = ∑ i ∈ s, φ i x * ψ i y` gives an operator
whose range lies in the span of the finitely many functions `φ i`, hence
finite rank.

These are general supporting results for the integral-operator material of
the v1 book `IntroductionToFunctionalAnalysis`. The Green kernel
`min x t * (1 - max x t)` in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean` and
`MathlibExt.Analysis.ODE.GreensOperator.greensKernel` is jointly continuous.
Its restriction to the interval square is a continuous-kernel example here.
The Volterra operator, with discontinuous indicator kernel `1_{y ≤ x}`, is
already provided by
`MathlibExt.Analysis.FunctionalAnalysis.VolterraOperator.volterraOperator`.
This general continuous-kernel construction is not a verbatim port of a
single v1 target.

Classical reference: F. Riesz and B. Sz.-Nagy, *Functional Analysis*,
§§89–90 (integral operators with continuous kernels are compact).

## Main declarations

* `kernelOperator k : C([0, 1], ℝ) →L[ℝ] C([0, 1], ℝ)` : the integral
  operator with kernel `k`.
* `kernelOperator_apply` : the evaluation formula.
* `norm_kernelOperator_le` : `‖kernelOperator k‖ ≤ ‖k‖`.
* `isCompactOperator_kernelOperator` : the kernel operator is compact.
* `finiteDimensional_range_kernelOperator_of_separable` : a separable
  kernel gives an operator of finite rank.
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.KernelOperator

open intervalIntegral
open scoped BoundedContinuousFunction Topology

noncomputable section

/-- The space `C([0, 1], ℝ)` of bounded continuous real functions on `[0, 1]`. -/
abbrev KernelSpace := Set.Icc (0 : ℝ) 1 →ᵇ ℝ

/-- A continuous kernel on `[0, 1] × [0, 1]`. -/
abbrev KernelType := (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) →ᵇ ℝ

/-- The clamped extension of a function on `[0, 1]` to `ℝ`. -/
def kernelExtend (f : KernelSpace) : ℝ → ℝ :=
  fun t => f (Set.projIcc 0 1 zero_le_one t)

/-- The clamped extension is continuous. -/
theorem kernelExtend_continuous (f : KernelSpace) : Continuous (kernelExtend f) :=
  f.continuous.comp continuous_projIcc

/-- On `[0, 1]` the clamped extension agrees with the original function. -/
theorem kernelExtend_apply_of_mem {f : KernelSpace} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    kernelExtend f t = f ⟨t, ht⟩ := by
  rw [kernelExtend, Set.projIcc_of_mem zero_le_one ht]

/-- The clamped extension is bounded by the sup norm. -/
theorem norm_kernelExtend_le (f : KernelSpace) (t : ℝ) : ‖kernelExtend f t‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

/-- The integrand of the kernel operator. -/
def kernelIntegrand (k : KernelType) (f : KernelSpace) (x : Set.Icc (0 : ℝ) 1) :
    ℝ → ℝ :=
  fun t => k (x, Set.projIcc 0 1 zero_le_one t) * kernelExtend f t

/-- The integrand is jointly continuous in `(x, t)`. -/
theorem continuous_kernelIntegrand_uncurry (k : KernelType) (f : KernelSpace) :
    Continuous (Function.uncurry (kernelIntegrand k f)) := by
  have h1 : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      k (p.1, Set.projIcc 0 1 zero_le_one p.2)) :=
    k.continuous.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))
  have h2 : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℝ => kernelExtend f p.2) :=
    (kernelExtend_continuous f).comp continuous_snd
  exact h1.mul h2

/-- The integrand is continuous in `t`. -/
theorem kernelIntegrand_continuous (k : KernelType) (f : KernelSpace)
    (x : Set.Icc (0 : ℝ) 1) : Continuous (kernelIntegrand k f x) :=
  (continuous_kernelIntegrand_uncurry k f).comp
    (continuous_const.prodMk continuous_id)

/-- The value of the kernel operator at `x`. -/
def kernelValue (k : KernelType) (f : KernelSpace) (x : Set.Icc (0 : ℝ) 1) : ℝ :=
  ∫ t in (0 : ℝ)..1, kernelIntegrand k f x t

/-- The kernel value is continuous in `x`. -/
theorem kernelValue_continuous (k : KernelType) (f : KernelSpace) :
    Continuous (kernelValue k f) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_kernelIntegrand_uncurry k f) 0 1

/-- The kernel value is bounded by `‖k‖ * ‖f‖`. -/
theorem norm_kernelValue_le (k : KernelType) (f : KernelSpace)
    (x : Set.Icc (0 : ℝ) 1) : ‖kernelValue k f x‖ ≤ ‖k‖ * ‖f‖ := by
  have hknorm : ∀ t, ‖k (x, Set.projIcc 0 1 zero_le_one t)‖ ≤ ‖k‖ :=
    fun t => k.norm_coe_le_norm _
  have hfnorm : ∀ t, ‖kernelExtend f t‖ ≤ ‖f‖ := norm_kernelExtend_le f
  calc ‖kernelValue k f x‖
      ≤ ∫ t in (0 : ℝ)..1, ‖kernelIntegrand k f x t‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ _t in (0 : ℝ)..1, ‖k‖ * ‖f‖ := by
        apply intervalIntegral.integral_mono_on zero_le_one
        · exact (kernelIntegrand_continuous k f x).norm.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro t _
          rw [kernelIntegrand, norm_mul]
          exact mul_le_mul (hknorm t) (hfnorm t) (norm_nonneg _) (norm_nonneg _)
    _ = ‖k‖ * ‖f‖ := by
        rw [intervalIntegral.integral_const]
        simp

/-- The kernel operator as a linear map. -/
noncomputable def kernelLinearMap (k : KernelType) : KernelSpace →ₗ[ℝ] KernelSpace where
  toFun f :=
    BoundedContinuousFunction.ofNormedAddCommGroup (kernelValue k f)
      (kernelValue_continuous k f) (‖k‖ * ‖f‖) (norm_kernelValue_le k f)
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    show kernelValue k (f + g) x = kernelValue k f x + kernelValue k g x
    simp only [kernelValue]
    rw [← intervalIntegral.integral_add
      ((kernelIntegrand_continuous k f x).intervalIntegrable _ _)
      ((kernelIntegrand_continuous k g x).intervalIntegrable _ _)]
    congr 1
    funext t
    simp [kernelIntegrand, kernelExtend, mul_add]
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro x
    show kernelValue k (c • f) x = c • kernelValue k f x
    simp only [kernelValue]
    rw [← intervalIntegral.integral_smul]
    congr 1
    funext t
    simp only [kernelIntegrand, kernelExtend, BoundedContinuousFunction.smul_apply,
      smul_eq_mul]
    ring

/-- The kernel operator is bounded on the unit ball. -/
theorem kernelLinearMap_norm_le (k : KernelType) (f : KernelSpace) :
    ‖kernelLinearMap k f‖ ≤ ‖k‖ * ‖f‖ := by
  show ‖BoundedContinuousFunction.ofNormedAddCommGroup (kernelValue k f)
      (kernelValue_continuous k f) (‖k‖ * ‖f‖) (norm_kernelValue_le k f)‖ ≤ ‖k‖ * ‖f‖
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (kernelValue_continuous k f) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (norm_kernelValue_le k f)

/-- The integral operator with continuous kernel `k` on `C([0, 1], ℝ)`. -/
noncomputable def kernelOperator (k : KernelType) : KernelSpace →L[ℝ] KernelSpace :=
  (kernelLinearMap k).mkContinuous ‖k‖ (kernelLinearMap_norm_le k)

/-- Evaluation formula for the kernel operator. -/
theorem kernelOperator_apply (k : KernelType) (f : KernelSpace)
    (x : Set.Icc (0 : ℝ) 1) :
    kernelOperator k f x = ∫ t in (0 : ℝ)..1, kernelIntegrand k f x t :=
  rfl

/-- The operator norm of the kernel operator is at most the sup norm of the kernel. -/
theorem norm_kernelOperator_le (k : KernelType) : ‖kernelOperator k‖ ≤ ‖k‖ :=
  (kernelOperator k).opNorm_le_bound (norm_nonneg _) (kernelLinearMap_norm_le k)

/-- A pointwise bound on the kernel difference gives a bound on the
difference of the values of the operator. -/
theorem norm_kernelOperator_apply_sub_le (k : KernelType) (f : KernelSpace)
    {x x' : Set.Icc (0 : ℝ) 1} {δ : ℝ}
    (h : ∀ y : Set.Icc (0 : ℝ) 1, ‖k (x, y) - k (x', y)‖ ≤ δ) :
    ‖kernelOperator k f x - kernelOperator k f x'‖ ≤ δ * ‖f‖ := by
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) (h ⟨0, le_refl 0, zero_le_one⟩)
  have hsub : kernelOperator k f x - kernelOperator k f x'
      = ∫ t in (0 : ℝ)..1,
          (k (x, Set.projIcc 0 1 zero_le_one t) -
            k (x', Set.projIcc 0 1 zero_le_one t)) * kernelExtend f t := by
    rw [kernelOperator_apply, kernelOperator_apply,
      ← intervalIntegral.integral_sub
        ((kernelIntegrand_continuous k f x).intervalIntegrable _ _)
        ((kernelIntegrand_continuous k f x').intervalIntegrable _ _)]
    congr 1
    funext t
    simp [kernelIntegrand, sub_mul]
  rw [hsub]
  calc ‖∫ t in (0 : ℝ)..1,
        (k (x, Set.projIcc 0 1 zero_le_one t) -
          k (x', Set.projIcc 0 1 zero_le_one t)) * kernelExtend f t‖
      ≤ ∫ t in (0 : ℝ)..1,
          ‖(k (x, Set.projIcc 0 1 zero_le_one t) -
            k (x', Set.projIcc 0 1 zero_le_one t)) * kernelExtend f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ = ∫ t in (0 : ℝ)..1,
        ‖k (x, Set.projIcc 0 1 zero_le_one t) -
          k (x', Set.projIcc 0 1 zero_le_one t)‖ * ‖kernelExtend f t‖ := by
        congr 1
        funext t
        rw [norm_mul]
    _ ≤ ∫ _t in (0 : ℝ)..1, δ * ‖f‖ := by
        have hcont_kdiff : Continuous (fun t =>
            k (x, Set.projIcc 0 1 zero_le_one t) -
              k (x', Set.projIcc 0 1 zero_le_one t)) :=
          (k.continuous.comp (continuous_const.prodMk continuous_projIcc)).sub
            (k.continuous.comp (continuous_const.prodMk continuous_projIcc))
        apply intervalIntegral.integral_mono_on zero_le_one
        · exact (hcont_kdiff.norm.mul
            (kernelExtend_continuous f).norm).intervalIntegrable (μ := MeasureTheory.volume) _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro t _
          exact mul_le_mul (h _) (norm_kernelExtend_le f t) (norm_nonneg _) hδ
    _ = δ * ‖f‖ := by
        rw [intervalIntegral.integral_const]
        simp

/-- The kernel operator is compact, by Arzelà–Ascoli: the image of the unit
ball is equicontinuous by uniform continuity of the kernel. -/
theorem isCompactOperator_kernelOperator (k : KernelType) :
    IsCompactOperator (kernelOperator k) := by
  refine (isCompactOperator_iff_isCompact_closure_image_ball
    (kernelOperator k : KernelSpace →ₗ[ℝ] KernelSpace) one_pos).mpr ?_
  refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 ‖k‖)
    (isCompact_closedBall (0 : ℝ) ‖k‖) _ ?_ ?_
  · intro g x hg
    obtain ⟨f, hf, rfl⟩ := hg
    have hf1 : ‖f‖ ≤ 1 := by
      have h := Metric.mem_ball.mp hf
      rw [dist_zero_right] at h
      exact le_of_lt h
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖kernelOperator k f x‖ ≤ ‖kernelOperator k f‖ :=
          BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ ‖k‖ * ‖f‖ := kernelLinearMap_norm_le k f
      _ ≤ ‖k‖ * 1 := mul_le_mul_of_nonneg_left hf1 (norm_nonneg _)
      _ = ‖k‖ := mul_one _
  · intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδk⟩ :=
      Metric.uniformContinuous_iff.mp
        (CompactSpace.uniformContinuous_of_continuous k.continuous) (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun x hx g => ?_⟩
    obtain ⟨f, hf, hfg⟩ := g.2
    have hf1 : ‖f‖ ≤ 1 := by
      have h := Metric.mem_ball.mp hf
      rw [dist_zero_right] at h
      exact le_of_lt h
    have hdist : ∀ y : Set.Icc (0 : ℝ) 1, ‖k (x₀, y) - k (x, y)‖ ≤ ε / 2 := by
      intro y
      have hxy : dist (x₀, y) (x, y) = dist x x₀ := by
        simp [Prod.dist_eq, dist_comm]
      have hlt := hδk (hxy ▸ hx)
      rw [dist_eq_norm] at hlt
      exact le_of_lt hlt
    rw [← hfg]
    show dist (kernelOperator k f x₀) (kernelOperator k f x) < ε
    rw [dist_eq_norm]
    calc ‖kernelOperator k f x₀ - kernelOperator k f x‖
        ≤ (ε / 2) * ‖f‖ := norm_kernelOperator_apply_sub_le k f hdist
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hf1 (le_of_lt (half_pos hε))
      _ = ε / 2 := mul_one _
      _ < ε := half_lt_self hε

/-- A separable kernel gives an operator of finite rank: its range lies in the
span of the finitely many functions `φ i`. -/
theorem finiteDimensional_range_kernelOperator_of_separable {ι : Type*} (k : KernelType)
    (s : Finset ι) (φ : ι → KernelSpace) (ψ : ι → KernelSpace)
    (hk : ∀ x y : Set.Icc (0 : ℝ) 1, k (x, y) = ∑ i ∈ s, φ i x * ψ i y) :
    FiniteDimensional ℝ ↥(LinearMap.range
      (kernelOperator k : KernelSpace →ₗ[ℝ] KernelSpace)) := by
  classical
  set M : Submodule ℝ KernelSpace := Submodule.span ℝ (φ '' (s : Set ι)) with hM
  have hMfin : FiniteDimensional ℝ M :=
    FiniteDimensional.span_of_finite ℝ ((Finset.finite_toSet s).image φ)
  have hrange : LinearMap.range (kernelOperator k : KernelSpace →ₗ[ℝ] KernelSpace) ≤ M := by
    rintro z ⟨f, rfl⟩
    show kernelOperator k f ∈ M
    have hform : kernelOperator k f
        = ∑ i ∈ s, (∫ t in (0 : ℝ)..1,
            ψ i (Set.projIcc 0 1 zero_le_one t) * kernelExtend f t) • φ i := by
      apply BoundedContinuousFunction.ext
      intro x
      have hsum : (∑ i ∈ s,
            (∫ t in (0 : ℝ)..1,
              ψ i (Set.projIcc 0 1 zero_le_one t) * kernelExtend f t) • φ i) x
          = ∑ i ∈ s,
            (∫ t in (0 : ℝ)..1,
              ψ i (Set.projIcc 0 1 zero_le_one t) * kernelExtend f t) * φ i x := by
        have h := map_sum (BoundedContinuousFunction.evalCLM ℝ x)
          (fun i => (∫ t in (0 : ℝ)..1,
            ψ i (Set.projIcc 0 1 zero_le_one t) * kernelExtend f t) • φ i) s
        simpa only [BoundedContinuousFunction.evalCLM_apply,
          BoundedContinuousFunction.smul_apply, smul_eq_mul] using h
      rw [kernelOperator_apply, hsum]
      have hcont : ∀ i : ι, Continuous (fun t =>
          φ i x *
            (ψ i (Set.projIcc 0 1 zero_le_one t) * kernelExtend f t)) := fun i =>
        continuous_const.mul
          (((ψ i).continuous.comp continuous_projIcc).mul (kernelExtend_continuous f))
      have hcong : (∫ t in (0 : ℝ)..1, kernelIntegrand k f x t)
          = ∫ t in (0 : ℝ)..1,
            ∑ i ∈ s, φ i x *
              (ψ i (Set.projIcc 0 1 zero_le_one t) * kernelExtend f t) := by
        apply intervalIntegral.integral_congr
        intro t _
        show k (x, Set.projIcc 0 1 zero_le_one t) * kernelExtend f t = _
        rw [hk x (Set.projIcc 0 1 zero_le_one t), Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc])
      rw [hcong, intervalIntegral.integral_finsetSum
        (fun i _ => (hcont i).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_const_mul, mul_comm]
    rw [hform]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨i, by simp [hi], rfl⟩
  exact Submodule.finiteDimensional_of_le hrange

/-- The kernel operator is additive in the kernel. -/
theorem kernelOperator_add (k₁ k₂ : KernelType) :
    kernelOperator (k₁ + k₂) = kernelOperator k₁ + kernelOperator k₂ := by
  apply ContinuousLinearMap.ext
  intro f
  apply BoundedContinuousFunction.ext
  intro x
  show (∫ t in (0 : ℝ)..1, kernelIntegrand (k₁ + k₂) f x t)
      = kernelOperator k₁ f x + kernelOperator k₂ f x
  rw [kernelOperator_apply, kernelOperator_apply,
    ← intervalIntegral.integral_add
      ((kernelIntegrand_continuous k₁ f x).intervalIntegrable _ _)
      ((kernelIntegrand_continuous k₂ f x).intervalIntegrable _ _)]
  congr 1
  funext t
  simp [kernelIntegrand, add_mul]

/-- The kernel operator is homogeneous in the kernel. -/
theorem kernelOperator_smul (c : ℝ) (k : KernelType) :
    kernelOperator (c • k) = c • kernelOperator k := by
  apply ContinuousLinearMap.ext
  intro f
  apply BoundedContinuousFunction.ext
  intro x
  show (∫ t in (0 : ℝ)..1, kernelIntegrand (c • k) f x t) = c • kernelOperator k f x
  rw [kernelOperator_apply, ← intervalIntegral.integral_smul]
  congr 1
  funext t
  simp [kernelIntegrand, smul_eq_mul, mul_assoc]

/-- The kernel operator with kernel `0` is `0`. -/
theorem kernelOperator_zero : kernelOperator 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply BoundedContinuousFunction.ext
  intro x
  rw [kernelOperator_apply]
  simp [kernelIntegrand]

end

end MathlibExt.Analysis.FunctionalAnalysis.KernelOperator

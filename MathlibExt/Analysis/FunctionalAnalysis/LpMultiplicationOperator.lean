/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multiplication operators on `L²`

For a σ-finite measure `μ` on `α` and an essentially bounded function
`φ : α → ℂ`, the multiplication operator `M_φ : L²(μ) →L[ℂ] L²(μ)` sends
`f` to `φ * f`. It is the `L²` counterpart of the multiplication operator on
`C(X, 𝕜)` (whose spectrum is the range of the multiplier) and of the diagonal
operator on `ℓ²` (whose spectrum is the closure of the range of the diagonal):
here the spectrum is the *essential range* of `φ`, and the operator norm is the
essential supremum norm of `φ`. A value `z` is an eigenvalue exactly when the
level set `{x | φ x = z}` has positive measure.

Classical reference: Rudin, *Functional Analysis*, 2nd edition,
Chapter 11 (multiplication operators / commutative Banach algebras), and
Chapter 12 (the `L²` case).

## Main declarations

* `essentialRange` : the essential range of a function with respect to a measure.
* `lpMulCLM` : the multiplication operator `M_φ` on `L²(μ)`.
* `lpMulCLM_apply` : its action, almost everywhere.
* `norm_lpMulCLM` : `‖M_φ‖ = (eLpNorm φ ∞ μ).toReal`.
* `spectrum_lpMulCLM` : `spectrum ℂ (M_φ) = essentialRange φ μ`.
* `hasEigenvalue_lpMulCLM_iff` : `z` is an eigenvalue of `M_φ` iff
  `0 < μ {x | φ x = z}`.
* `essentialRange_const`, `essentialRange_count_eq_range` : computations of the
  essential range for constant functions and for counting measure on a finite type.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.LpMultiplicationOperator

open Set Filter MeasureTheory Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]

/-- The essential range of `φ` with respect to `μ`: the set of `z` such that
`φ` comes arbitrarily close to `z` on sets of positive measure. -/
def essentialRange (φ : α → ℂ) (μ : Measure α) : Set ℂ :=
  {z | ∀ ε > 0, 0 < μ (φ ⁻¹' Metric.ball z ε)}

omit [SigmaFinite μ] in
theorem mem_essentialRange {φ : α → ℂ} {z : ℂ} :
    z ∈ essentialRange φ μ ↔ ∀ ε > 0, 0 < μ (φ ⁻¹' Metric.ball z ε) :=
  Iff.rfl

omit [SigmaFinite μ] in
/-- The essential range depends only on the almost-everywhere class of `φ`. -/
theorem essentialRange_congr_ae {φ ψ : α → ℂ} (h : φ =ᵐ[μ] ψ) :
    essentialRange φ μ = essentialRange ψ μ := by
  ext z
  constructor
  · intro hz ε hε
    have hae : (φ ⁻¹' Metric.ball z ε) =ᵐ[μ] (ψ ⁻¹' Metric.ball z ε) := by
      filter_upwards [h] with x hx
      simp only [Set.mem_preimage, Metric.mem_ball, hx]
    rw [← MeasureTheory.measure_congr hae]
    exact hz ε hε
  · intro hz ε hε
    have hae : (ψ ⁻¹' Metric.ball z ε) =ᵐ[μ] (φ ⁻¹' Metric.ball z ε) := by
      filter_upwards [h.symm] with x hx
      simp only [Set.mem_preimage, Metric.mem_ball, hx]
    rw [← MeasureTheory.measure_congr hae]
    exact hz ε hε

omit [SigmaFinite μ] in
/-- A point outside the essential range is bounded away from the values of `φ`
on a set of full measure. -/
theorem not_mem_essentialRange_iff {φ : α → ℂ} {z : ℂ} :
    z ∉ essentialRange φ μ ↔ ∃ ε > 0, μ (φ ⁻¹' Metric.ball z ε) = 0 := by
  simp only [essentialRange, Set.mem_ofPred_eq, not_forall, not_lt]
  constructor
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε, hε, le_antisymm h bot_le⟩
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε, hε, by rw [h]⟩

omit [SigmaFinite μ] in
/-- The essential range of a constant function is the singleton of the constant,
provided the whole space has positive measure. -/
theorem essentialRange_const {c : ℂ} (hμ : μ univ ≠ 0) :
    essentialRange (fun _ => c) μ = {c} := by
  ext z
  simp only [essentialRange, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hz
    by_contra hne
    have hε : 0 < dist z c := dist_pos.mpr hne
    have h0 := hz (dist z c) hε
    have hempty : (fun _ : α => c) ⁻¹' Metric.ball z (dist z c) = ∅ := by
      ext x
      simp [Metric.mem_ball, dist_comm]
    rw [hempty, MeasureTheory.measure_empty] at h0
    exact lt_irrefl 0 h0
  · intro hzc ε hε
    have huniv : (fun _ : α => c) ⁻¹' Metric.ball z ε = univ := by
      ext x
      simp [Metric.mem_ball, hzc, hε]
    rw [huniv]
    exact pos_iff_ne_zero.mpr hμ

/-- For counting measure on a finite type with measurable singletons, the
essential range is the range. -/
theorem essentialRange_count_eq_range [Finite α] [MeasurableSingletonClass α]
    (φ : α → ℂ) :
    essentialRange φ (Measure.count : Measure α) = Set.range φ := by
  ext z
  simp only [essentialRange, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hz
    have hclosure : z ∈ closure (Set.range φ) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hne : (φ ⁻¹' Metric.ball z ε).Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        have h0 := hz ε hε
        rw [hne, MeasureTheory.measure_empty] at h0
        exact lt_irrefl 0 h0
      obtain ⟨x, hx⟩ := hne
      refine ⟨φ x, ⟨x, rfl⟩, ?_⟩
      rw [dist_comm]
      simpa using hx
    rwa [(Set.Finite.isClosed (Set.finite_range φ)).closure_eq] at hclosure
  · rintro ⟨x₀, hx₀⟩ ε hε
    have hsub : {x₀} ⊆ φ ⁻¹' Metric.ball z ε := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [Set.mem_preimage, Metric.mem_ball, hx₀, dist_self]
      exact hε
    calc 0 < (Measure.count : Measure α) {x₀} := by
          rw [Measure.count_singleton]; exact one_pos
      _ ≤ (Measure.count : Measure α) (φ ⁻¹' Metric.ball z ε) :=
          MeasureTheory.measure_mono hsub

omit [SigmaFinite μ] in
/-- A constant function is essentially bounded. -/
theorem memLp_const_top (c : ℂ) : MemLp (fun _ => c) ∞ μ := by
  apply memLp_top_of_bound aestronglyMeasurable_const ‖c‖
  filter_upwards with x
  exact le_refl _

omit [SigmaFinite μ] in
/-- Multiplying an `L²` function by an essentially bounded function stays in `L²`. -/
theorem memLp_mul_of_memLp_top {φ : α → ℂ} (hφ : MemLp φ ∞ μ)
    (f : Lp ℂ 2 μ) : MemLp (fun x => φ x * f x) 2 μ := by
  have hle : eLpNorm (fun x => φ x * f x) 2 μ ≤
      1 * eLpNorm φ ∞ μ * eLpNorm (f : α → ℂ) 2 μ := by
    apply eLpNorm_le_eLpNorm_top_mul_eLpNorm (2 : ℝ≥0∞) (fun a b => a * b) 1
      (continuous_fst.mul continuous_snd :
      Continuous (Function.uncurry fun a b : ℂ => a * b)) hφ.aestronglyMeasurable
    filter_upwards with x
    simp [nnnorm_mul]
  refine hle.trans_lt ?_
  rw [one_mul]
  exact ENNReal.mul_lt_top hφ.eLpNorm_lt_top (Lp.memLp f).eLpNorm_lt_top

/-- The multiplication operator `M_φ` on `L²(μ)`: `M_φ f = φ * f`. -/
noncomputable def lpMulCLM (φ : α → ℂ) (hφ : MemLp φ ∞ μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul_of_memLp_top hφ f).toLp (fun x => φ x * f x)
      map_add' := by
        intro f g
        apply Lp.ext
        calc ⇑((memLp_mul_of_memLp_top hφ (f + g)).toLp (fun x => φ x * (f + g) x))
            =ᵐ[μ] fun x => φ x * (f + g) x := MemLp.coeFn_toLp _
          _ =ᵐ[μ] fun x => φ x * (f x + g x) := by
              filter_upwards [Lp.coeFn_add f g] with x hx
              rw [hx, Pi.add_apply]
          _ =ᵐ[μ] fun x => φ x * f x + φ x * g x :=
            Filter.Eventually.of_forall fun x => mul_add _ _ _
          _ =ᵐ[μ] ⇑((memLp_mul_of_memLp_top hφ f).toLp (fun x => φ x * f x) +
              (memLp_mul_of_memLp_top hφ g).toLp (fun x => φ x * g x)) :=
              (Lp.coeFn_add _ _).trans
                ((MemLp.coeFn_toLp _).add (MemLp.coeFn_toLp _)) |>.symm
      map_smul' := by
        intro c f
        apply Lp.ext
        calc ⇑((memLp_mul_of_memLp_top hφ (c • f)).toLp (fun x => φ x * (c • f) x))
            =ᵐ[μ] fun x => φ x * (c • f) x := MemLp.coeFn_toLp _
          _ =ᵐ[μ] fun x => φ x * (c * f x) := by
              filter_upwards [Lp.coeFn_smul c f] with x hx
              rw [hx, Pi.smul_apply, smul_eq_mul]
          _ =ᵐ[μ] fun x => c * (φ x * f x) :=
            Filter.Eventually.of_forall fun x => by ring
          _ =ᵐ[μ] ⇑(c • (memLp_mul_of_memLp_top hφ f).toLp (fun x => φ x * f x)) :=
              (Lp.coeFn_smul c _).trans (by
                filter_upwards [MemLp.coeFn_toLp (memLp_mul_of_memLp_top hφ f)] with x hx
                simp only [Pi.smul_apply, smul_eq_mul, hx]) |>.symm }
    (eLpNorm φ ∞ μ).toReal
    (by
      intro f
      show ‖(memLp_mul_of_memLp_top hφ f).toLp (fun x => φ x * f x)‖ ≤
        (eLpNorm φ ∞ μ).toReal * ‖f‖
      have hle : eLpNorm (fun x => φ x * f x) 2 μ ≤
          eLpNorm φ ∞ μ * eLpNorm (f : α → ℂ) 2 μ := by
        have h := eLpNorm_le_eLpNorm_top_mul_eLpNorm (2 : ℝ≥0∞) (fun a b => a * b) 1
          (continuous_fst.mul continuous_snd :
      Continuous (Function.uncurry fun a b : ℂ => a * b)) hφ.aestronglyMeasurable (f := φ)
          (g := (f : α → ℂ)) (by filter_upwards with x; simp [nnnorm_mul])
        simpa using h
      rw [Lp.norm_toLp]
      calc (eLpNorm (fun x => φ x * f x) 2 μ).toReal
          ≤ (eLpNorm φ ∞ μ * eLpNorm (f : α → ℂ) 2 μ).toReal :=
            ENNReal.toReal_mono
              (ENNReal.mul_ne_top hφ.eLpNorm_ne_top (Lp.eLpNorm_ne_top f)) hle
        _ = (eLpNorm φ ∞ μ).toReal * ‖f‖ := by
            rw [ENNReal.toReal_mul, Lp.norm_def])

omit [SigmaFinite μ] in
@[simp]
theorem lpMulCLM_apply {φ : α → ℂ} (hφ : MemLp φ ∞ μ) (f : Lp ℂ 2 μ) :
    ⇑(lpMulCLM φ hφ f) =ᵐ[μ] fun x => φ x * f x := by
  rw [lpMulCLM, LinearMap.mkContinuous_apply]
  exact MemLp.coeFn_toLp (memLp_mul_of_memLp_top hφ f)

omit [SigmaFinite μ] in
/-- The multiplication operator depends only on the almost-everywhere class of
the multiplier. -/
theorem lpMulCLM_congr_ae {φ ψ : α → ℂ} (h : φ =ᵐ[μ] ψ) (hφ : MemLp φ ∞ μ)
    (hψ : MemLp ψ ∞ μ) : lpMulCLM φ hφ = lpMulCLM ψ hψ := by
  ext f
  exact (lpMulCLM_apply hφ f).trans (by
    filter_upwards [h, lpMulCLM_apply hψ f] with x hx hx2
    rw [hx, hx2])

omit [SigmaFinite μ] in
/-- Multiplication by the constant function `c` is scalar multiplication by `c`. -/
theorem lpMulCLM_const_apply (c : ℂ) (f : Lp ℂ 2 μ) :
    lpMulCLM (fun _ => c) (memLp_const_top c) f = c • f := by
  apply Lp.ext
  filter_upwards [lpMulCLM_apply (memLp_const_top c) f, Lp.coeFn_smul c f] with x hx1 hx2
  rw [hx1, hx2, Pi.smul_apply, smul_eq_mul]

omit [SigmaFinite μ] in
/-- Multiplication by the constant function `1` is the identity. -/
theorem lpMulCLM_one : lpMulCLM (fun _ : α => (1 : ℂ)) (memLp_const_top (1 : ℂ))
    = (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
  ext f
  rw [lpMulCLM_const_apply]
  simp

omit [SigmaFinite μ] in
/-- The product law for multiplication operators. -/
theorem lpMulCLM_mul {φ ψ : α → ℂ} (hφ : MemLp φ ∞ μ) (hψ : MemLp ψ ∞ μ)
    (hφψ : MemLp (fun x => φ x * ψ x) ∞ μ) :
    lpMulCLM (fun x => φ x * ψ x) hφψ = lpMulCLM φ hφ * lpMulCLM ψ hψ := by
  ext f
  show ⇑((lpMulCLM (fun x => φ x * ψ x) hφψ) f) =ᵐ[μ]
    ⇑(lpMulCLM φ hφ (lpMulCLM ψ hψ f))
  filter_upwards [lpMulCLM_apply hφψ f, lpMulCLM_apply hψ f,
    lpMulCLM_apply hφ (lpMulCLM ψ hψ f)] with x hx1 hx2 hx3
  rw [hx1, hx3, hx2, mul_assoc]

omit [SigmaFinite μ] in
/-- Subtracting the multiplication operator from a scalar is multiplication by
the pointwise difference. -/
theorem algebraMap_sub_lpMulCLM {φ : α → ℂ} (hφ : MemLp φ ∞ μ) (z : ℂ)
    (h : MemLp (fun x => z - φ x) ∞ μ) :
    algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z - lpMulCLM φ hφ =
      lpMulCLM (fun x => z - φ x) h := by
  ext f
  have hAlg : (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z) f = z • f := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp
  filter_upwards [Lp.coeFn_sub ((algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z) f)
    (lpMulCLM φ hφ f), Lp.coeFn_smul z f, lpMulCLM_apply hφ f, lpMulCLM_apply h f]
    with x hx1 hx2 hx3 hx4
  show ⇑((algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z) f - lpMulCLM φ hφ f) x = _
  rw [hx1, hAlg, Pi.sub_apply, hx2, Pi.smul_apply, smul_eq_mul, hx3, hx4, sub_mul]

omit [SigmaFinite μ] in
/-- Every essentially bounded function has a measurable representative in the
same almost-everywhere class (hence with the same multiplication operator). -/
theorem exists_measurable_memLp {φ : α → ℂ} (hφ : MemLp φ ∞ μ) :
    ∃ ψ : α → ℂ, Measurable ψ ∧ φ =ᵐ[μ] ψ ∧ MemLp ψ ∞ μ := by
  obtain ⟨ψ, hψ, hψae⟩ := hφ.aestronglyMeasurable
  exact ⟨ψ, hψ.measurable, hψae, MemLp.ae_eq hψae hφ⟩

omit [SigmaFinite μ] in
/-- Almost everywhere, `‖φ x‖` is at most the essential supremum norm. -/
theorem ae_norm_le_eLpNorm_top {φ : α → ℂ} (hφ : MemLp φ ∞ μ) :
    ∀ᵐ x ∂μ, ‖φ x‖ ≤ (eLpNorm φ ∞ μ).toReal := by
  have h := ae_le_eLpNormEssSup (f := φ) (μ := μ)
  filter_upwards [h] with x hx
  rw [← eLpNorm_exponent_top hφ.aestronglyMeasurable] at hx
  have hx2 : (‖φ x‖ₑ).toReal ≤ (eLpNorm φ ∞ μ).toReal :=
    ENNReal.toReal_mono hφ.eLpNorm_ne_top hx
  simpa using hx2

omit [SigmaFinite μ] in
/-- A pointwise almost-everywhere bound on the multiplier bounds the operator
applied to any vector. -/
theorem norm_lpMulCLM_apply_le_of_ae_bound {φ : α → ℂ} (hφ : MemLp φ ∞ μ) {C : ℝ}
    (f : Lp ℂ 2 μ) (hC : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C) :
    ‖lpMulCLM φ hφ f‖ ≤ C * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [lpMulCLM_apply hφ f, hC] with x hx hCx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hCx (norm_nonneg _)

omit [SigmaFinite μ] in
/-- A bound on the multiplier that holds almost everywhere on the support of `f`
bounds the operator applied to `f`. -/
theorem norm_lpMulCLM_apply_le_of_ae_support {φ : α → ℂ} (hφ : MemLp φ ∞ μ) {C : ℝ}
    (f : Lp ℂ 2 μ) (hC : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C ∨ f x = 0) :
    ‖lpMulCLM φ hφ f‖ ≤ C * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [lpMulCLM_apply hφ f, hC] with x hx hCx
  rw [hx, norm_mul]
  rcases hCx with hle | h0
  · exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  · rw [h0, norm_zero, mul_zero, mul_zero]

omit [SigmaFinite μ] in
/-- A pointwise almost-everywhere lower bound on the multiplier, tested on a unit
vector, lower-bounds the operator norm. -/
theorem le_norm_lpMulCLM_of_ae_le {φ : α → ℂ} (hφ : MemLp φ ∞ μ) {C : ℝ}
    (hC0 : 0 ≤ C) {f : Lp ℂ 2 μ} (hf : ‖f‖ = 1)
    (h : ∀ᵐ x ∂μ, C * ‖f x‖ ≤ ‖φ x‖ * ‖f x‖) : C ≤ ‖lpMulCLM φ hφ‖ := by
  have hCnorm : ‖((C : ℂ))‖ = C := by simp [abs_of_nonneg hC0]
  have h1 : ‖((C : ℂ)) • f‖ ≤ 1 * ‖lpMulCLM φ hφ f‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) (f := ((C : ℂ)) • f)
      (g := lpMulCLM φ hφ f) ?_
    filter_upwards [Lp.coeFn_smul ((C : ℂ)) f, lpMulCLM_apply hφ f, h] with x hx1 hx2 hx3
    rw [hx1, hx2]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, one_mul]
    rw [hCnorm]
    exact hx3
  have h2 : ‖((C : ℂ)) • f‖ = C := by
    rw [norm_smul, hCnorm, hf, mul_one]
  have h3 : ‖lpMulCLM φ hφ f‖ ≤ ‖lpMulCLM φ hφ‖ := by
    calc ‖lpMulCLM φ hφ f‖ ≤ ‖lpMulCLM φ hφ‖ * ‖f‖ := (lpMulCLM φ hφ).le_opNorm f
      _ = ‖lpMulCLM φ hφ‖ := by rw [hf, mul_one]
  rw [h2, one_mul] at h1
  exact h1.trans h3

omit [SigmaFinite μ] in
/-- The operator norm is at most the essential supremum norm of the multiplier. -/
theorem norm_lpMulCLM_le {φ : α → ℂ} (hφ : MemLp φ ∞ μ) :
    ‖lpMulCLM φ hφ‖ ≤ (eLpNorm φ ∞ μ).toReal := by
  refine ContinuousLinearMap.opNorm_le_bound (lpMulCLM φ hφ)
    (M := (eLpNorm φ ∞ μ).toReal) ENNReal.toReal_nonneg ?_
  intro f
  exact norm_lpMulCLM_apply_le_of_ae_bound hφ f (ae_norm_le_eLpNorm_top hφ)

omit [SigmaFinite μ] in
/-- A normalized indicator of a set of finite positive measure: a unit vector
supported on the set, used as a test vector for the norm, spectrum, and
eigenvalue arguments. -/
theorem exists_unit_vector {t : Set α} (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (hpos : 0 < μ t) :
    ∃ u : Lp ℂ 2 μ, ‖u‖ = 1 ∧
      (∀ᵐ x ∂μ, x ∈ t → u x = (RCLike.ofReal ((μ t).toReal ^ (-1 / 2 : ℝ)) : ℂ)) ∧
      (∀ᵐ x ∂μ, x ∉ t → u x = 0) := by
  refine ⟨(RCLike.ofReal ((μ t).toReal ^ (-1 / 2 : ℝ)) : ℂ) • indicatorConstLp 2 ht hμt (1 : ℂ), ?_, ?_, ?_⟩
  · have hreal : 0 < (μ t).toReal := ENNReal.toReal_pos hpos.ne' hμt
    have hscalar : ‖(RCLike.ofReal ((μ t).toReal ^ (-1 / 2 : ℝ)) : ℂ)‖
        = (μ t).toReal ^ (-1 / 2 : ℝ) := by
      rw [RCLike.norm_ofReal, abs_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    rw [norm_smul, hscalar,
      norm_indicatorConstLp (by simp) (by simp), norm_one, one_mul, measureReal_def]
    have hexp : (1 : ℝ) / (2 : ℝ≥0∞).toReal = 1 / 2 := by simp
    rw [hexp, ← Real.rpow_add hreal, show (-1 / 2 : ℝ) + 1 / 2 = 0 by norm_num,
      Real.rpow_zero]
  · have hmem : ∀ᵐ x ∂μ, x ∈ t → indicatorConstLp 2 ht hμt (1 : ℂ) x = (1 : ℂ) :=
      indicatorConstLp_coeFn_mem
    filter_upwards [Lp.coeFn_smul ((RCLike.ofReal ((μ t).toReal ^ (-1 / 2 : ℝ)) : ℂ))
      (indicatorConstLp 2 ht hμt (1 : ℂ)), hmem] with x hx hmemx
    intro hxt
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul, hmemx hxt, mul_one]
  · have hnot : ∀ᵐ x ∂μ, x ∉ t → indicatorConstLp 2 ht hμt (1 : ℂ) x = 0 :=
      indicatorConstLp_coeFn_notMem
    filter_upwards [Lp.coeFn_smul ((RCLike.ofReal ((μ t).toReal ^ (-1 / 2 : ℝ)) : ℂ))
      (indicatorConstLp 2 ht hμt (1 : ℂ)), hnot] with x hx hnotx
    intro hxt
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul, hnotx hxt, mul_zero]

/-- The operator norm equals the essential supremum norm, for a measurable
multiplier. -/
theorem norm_lpMulCLM_of_measurable {φ : α → ℂ} (hφ : MemLp φ ∞ μ)
    (hφm : Measurable φ) : ‖lpMulCLM φ hφ‖ = (eLpNorm φ ∞ μ).toReal := by
  apply le_antisymm (norm_lpMulCLM_le hφ)
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hCgt, hClt⟩ := exists_between hcon
  have hC0 : 0 < C := lt_of_le_of_lt (norm_nonneg _) hCgt
  have hpos : 0 < μ {x | C < ‖φ x‖} := by
    by_contra hcon2
    push Not at hcon2
    have h0 : μ {x | C < ‖φ x‖} = 0 := le_antisymm hcon2 bot_le
    have hae : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C := by
      rw [MeasureTheory.ae_iff]
      have hset : {x : α | ¬ ‖φ x‖ ≤ C} = {x | C < ‖φ x‖} := by
        ext x
        simp [not_le]
      rw [hset]
      exact h0
    have hess : eLpNormEssSup φ μ ≤ ENNReal.ofReal C := eLpNormEssSup_le_of_ae_bound hae
    have htop : (eLpNorm φ ∞ μ).toReal ≤ C := by
      rw [eLpNorm_exponent_top hφ.aestronglyMeasurable]
      calc (eLpNormEssSup φ μ).toReal ≤ (ENNReal.ofReal C).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
        _ = C := ENNReal.toReal_ofReal hC0.le
    exact not_lt_of_ge htop hClt
  obtain ⟨t, htmeas, htsub, hpos_t, htop_t⟩ :=
    MeasureTheory.Measure.exists_subset_measure_lt_top
      (measurableSet_lt measurable_const hφm.norm) hpos
  obtain ⟨u, hu_norm, hu_mem, hu_notmem⟩ := exists_unit_vector htmeas htop_t.ne hpos_t
  have hle : C ≤ ‖lpMulCLM φ hφ‖ := by
    apply le_norm_lpMulCLM_of_ae_le hφ hC0.le hu_norm
    filter_upwards [hu_mem, hu_notmem] with x hx_mem hx_notmem
    by_cases hxt : x ∈ t
    · have hCφ : C ≤ ‖φ x‖ := le_of_lt (htsub hxt)
      have hscalar : ‖(RCLike.ofReal ((μ t).toReal ^ (-1 / 2 : ℝ)) : ℂ)‖
          = (μ t).toReal ^ (-1 / 2 : ℝ) := by
        rw [RCLike.norm_ofReal, abs_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
      rw [hx_mem hxt, hscalar]
      exact mul_le_mul_of_nonneg_right hCφ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    · rw [hx_notmem hxt]
      simp
  exact not_lt_of_ge hle hCgt

/-- The operator norm equals the essential supremum norm of the multiplier. -/
theorem norm_lpMulCLM {φ : α → ℂ} (hφ : MemLp φ ∞ μ) :
    ‖lpMulCLM φ hφ‖ = (eLpNorm φ ∞ μ).toReal := by
  obtain ⟨ψ, hψmeas, hψae, hψ⟩ := exists_measurable_memLp hφ
  rw [lpMulCLM_congr_ae hψae hφ hψ, eLpNorm_congr_ae hψae]
  exact norm_lpMulCLM_of_measurable hψ hψmeas

/-- The spectrum is the essential range, for a measurable multiplier. -/
theorem spectrum_lpMulCLM_of_measurable {φ : α → ℂ} (hφ : MemLp φ ∞ μ)
    (hφm : Measurable φ) : spectrum ℂ (lpMulCLM φ hφ) = essentialRange φ μ := by
  ext z
  constructor
  · intro hz
    by_contra hze
    rw [not_mem_essentialRange_iff] at hze
    obtain ⟨ε, hε, hε0⟩ := hze
    have hae : ∀ᵐ x ∂μ, x ∉ φ ⁻¹' Metric.ball z ε := by
      rw [MeasureTheory.ae_iff]
      have hset : {x : α | ¬ x ∉ φ ⁻¹' Metric.ball z ε} = φ ⁻¹' Metric.ball z ε := by
        ext x
        simp
      rw [hset]
      exact hε0
    have hψae : ∀ᵐ x ∂μ, ‖(z - φ x)⁻¹‖ ≤ ε⁻¹ := by
      filter_upwards [hae] with x hx
      have hdist : ε ≤ dist (φ x) z := le_of_not_gt (by
        intro hlt
        exact hx (by rw [Set.mem_preimage, Metric.mem_ball]; exact hlt))
      have hnorm : ε ≤ ‖z - φ x‖ := by
        have h1 : dist (φ x) z = ‖φ x - z‖ := dist_eq_norm _ _
        rw [h1, norm_sub_rev] at hdist
        exact hdist
      have hnorm_pos : 0 < ‖z - φ x‖ := hε.trans_le hnorm
      rw [norm_inv]
      exact (inv_le_inv₀ hnorm_pos hε).mpr hnorm
    have hψ : MemLp (fun x => (z - φ x)⁻¹) ∞ μ :=
      memLp_top_of_bound ((measurable_const.sub hφm).inv).aestronglyMeasurable ε⁻¹ hψae
    have hzφ : MemLp (fun x => z - φ x) ∞ μ := (memLp_const_top z).sub hφ
    have hne : ∀ᵐ x ∂μ, z - φ x ≠ 0 := by
      filter_upwards [hae] with x hx
      intro hzero
      apply hx
      rw [Set.mem_preimage, Metric.mem_ball]
      have hφx : z = φ x := sub_eq_zero.mp hzero
      rw [hφx, dist_self]
      exact hε
    have hprod1 : (fun x => (z - φ x) * (z - φ x)⁻¹) =ᵐ[μ] (fun _ => 1) := by
      filter_upwards [hne] with x hx
      exact mul_inv_cancel₀ hx
    have hprod2 : (fun x => (z - φ x)⁻¹ * (z - φ x)) =ᵐ[μ] (fun _ => 1) := by
      filter_upwards [hne] with x hx
      exact inv_mul_cancel₀ hx
    have hprod1Mem : MemLp (fun x => (z - φ x) * (z - φ x)⁻¹) ∞ μ :=
      MemLp.ae_eq hprod1.symm (memLp_const_top (1 : ℂ))
    have hprod2Mem : MemLp (fun x => (z - φ x)⁻¹ * (z - φ x)) ∞ μ :=
      MemLp.ae_eq hprod2.symm (memLp_const_top (1 : ℂ))
    have hIsUnit : IsUnit (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z - lpMulCLM φ hφ) := by
      have hdecomp : algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z - lpMulCLM φ hφ =
          lpMulCLM (fun x => z - φ x) hzφ := algebraMap_sub_lpMulCLM hφ z hzφ
      refine ⟨⟨lpMulCLM (fun x => z - φ x) hzφ, lpMulCLM (fun x => (z - φ x)⁻¹) hψ,
        ?_, ?_⟩, hdecomp.symm⟩
      · rw [← lpMulCLM_mul hzφ hψ hprod1Mem,
          lpMulCLM_congr_ae hprod1 hprod1Mem (memLp_const_top (1 : ℂ))]
        exact lpMulCLM_one
      · rw [← lpMulCLM_mul hψ hzφ hprod2Mem,
          lpMulCLM_congr_ae hprod2 hprod2Mem (memLp_const_top (1 : ℂ))]
        exact lpMulCLM_one
    exact (spectrum.mem_iff.mp hz) hIsUnit
  · intro hze
    rw [spectrum.mem_iff]
    intro hUnit
    obtain ⟨S, hS⟩ := hUnit.exists_left_inv
    have hzφ : MemLp (fun x => z - φ x) ∞ μ := (memLp_const_top z).sub hφ
    rw [algebraMap_sub_lpMulCLM hφ z hzφ] at hS
    have hbound : ∀ m : ℕ, 1 ≤ ‖S‖ * (1 / ((m : ℝ) + 1)) := by
      intro m
      have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      have hmeas : MeasurableSet (φ ⁻¹' Metric.ball z (1 / ((m : ℝ) + 1))) :=
        hφm (measurableSet_ball)
      have hpos : 0 < μ (φ ⁻¹' Metric.ball z (1 / ((m : ℝ) + 1))) := hze _ hε
      obtain ⟨t, htmeas, htsub, hpos_t, htop_t⟩ :=
        MeasureTheory.Measure.exists_subset_measure_lt_top hmeas hpos
      obtain ⟨u, hu_norm, hu_mem, hu_notmem⟩ := exists_unit_vector htmeas htop_t.ne hpos_t
      have hMu : ‖lpMulCLM (fun x => z - φ x) hzφ u‖ ≤ 1 / ((m : ℝ) + 1) := by
        have h := norm_lpMulCLM_apply_le_of_ae_support hzφ u (C := 1 / ((m : ℝ) + 1)) (by
          filter_upwards [hu_mem, hu_notmem] with x hx_mem hx_notmem
          by_cases hxt : x ∈ t
          · left
            have hlt : dist (φ x) z < 1 / ((m : ℝ) + 1) := htsub hxt
            have hnorm : ‖z - φ x‖ = dist (φ x) z := by
              rw [dist_eq_norm, norm_sub_rev]
            rw [hnorm]
            exact hlt.le
          · right
            exact hx_notmem hxt)
        rwa [hu_norm, mul_one] at h
      have hSeq : S (lpMulCLM (fun x => z - φ x) hzφ u) = u := by
        have h1 : (S * lpMulCLM (fun x => z - φ x) hzφ) u = u := by
          rw [hS]
          exact IsOneApplyEqSelf.one_apply_eq_self _
        exact h1
      calc 1 = ‖u‖ := hu_norm.symm
        _ = ‖S (lpMulCLM (fun x => z - φ x) hzφ u)‖ := by rw [hSeq]
        _ ≤ ‖S‖ * ‖lpMulCLM (fun x => z - φ x) hzφ u‖ := S.le_opNorm _
        _ ≤ ‖S‖ * (1 / ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hMu (norm_nonneg _)
    rcases eq_or_ne ‖S‖ 0 with hS0 | hS0
    · have h0 := hbound 0
      rw [hS0] at h0
      norm_num at h0
    · obtain ⟨n, hn⟩ := exists_nat_gt ‖S‖
      have hlt : ‖S‖ * (1 / ((n : ℝ) + 1)) < 1 := by
        have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        calc ‖S‖ * (1 / ((n : ℝ) + 1))
            < ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) :=
              mul_lt_mul_of_pos_right (by linarith) (by positivity)
          _ = 1 := by
              rw [mul_one_div, div_self h1.ne']
      exact not_lt_of_ge (hbound n) hlt

/-- The spectrum of the multiplication operator is the essential range of the
multiplier. -/
theorem spectrum_lpMulCLM {φ : α → ℂ} (hφ : MemLp φ ∞ μ) :
    spectrum ℂ (lpMulCLM φ hφ) = essentialRange φ μ := by
  obtain ⟨ψ, hψmeas, hψae, hψ⟩ := exists_measurable_memLp hφ
  rw [lpMulCLM_congr_ae hψae hφ hψ, essentialRange_congr_ae hψae]
  exact spectrum_lpMulCLM_of_measurable hψ hψmeas

/-- The eigenvalue criterion, for a measurable multiplier. -/
theorem hasEigenvalue_lpMulCLM_iff_of_measurable {φ : α → ℂ} (hφ : MemLp φ ∞ μ)
    (hφm : Measurable φ) (z : ℂ) :
    Module.End.HasEigenvalue (lpMulCLM φ hφ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) z ↔
      0 < μ {x | φ x = z} := by
  constructor
  · intro hz
    obtain ⟨v, hv_mem, hv0⟩ := hz.exists_hasEigenvector
    have hveq : lpMulCLM φ hφ v = z • v :=
      (Module.End.mem_eigenspace_iff).mp hv_mem
    by_contra hcon
    push Not at hcon
    have hset0 : μ {x | φ x = z} = 0 := le_antisymm hcon bot_le
    have hae : ∀ᵐ x ∂μ, x ∉ {x | φ x = z} := by
      rw [MeasureTheory.ae_iff]
      have hset : {x : α | ¬ x ∉ {x | φ x = z}} = {x | φ x = z} := by
        ext x
        simp
      rw [hset]
      exact hset0
    have hzero : ∀ᵐ x ∂μ, v x = 0 := by
      filter_upwards [lpMulCLM_apply hφ v, Lp.coeFn_smul z v, hae] with x hx1 hx2 hx4
      have hx3 : (lpMulCLM φ hφ v) x = (z • v) x := by rw [hveq]
      rw [hx1, hx2, Pi.smul_apply, smul_eq_mul] at hx3
      have hne : φ x - z ≠ 0 := sub_ne_zero.mpr hx4
      have hprod : (φ x - z) * v x = 0 := by
        rw [sub_mul, sub_eq_zero]
        exact hx3
      exact (mul_eq_zero.mp hprod).resolve_left hne
    have hvzero : v = 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      exact hzero
    exact hv0 hvzero
  · intro hpos
    have hmeas : MeasurableSet {x | φ x = z} := hφm (measurableSet_singleton z)
    obtain ⟨t, htmeas, htsub, hpos_t, htop_t⟩ :=
      MeasureTheory.Measure.exists_subset_measure_lt_top hmeas hpos
    obtain ⟨u, hu_norm, hu_mem, hu_notmem⟩ := exists_unit_vector htmeas htop_t.ne hpos_t
    have hMu : lpMulCLM φ hφ u = z • u := by
      apply Lp.ext
      filter_upwards [lpMulCLM_apply hφ u, Lp.coeFn_smul z u, hu_mem, hu_notmem]
        with x hx1 hx2 hx3 hx4
      rw [hx1, hx2, Pi.smul_apply, smul_eq_mul]
      by_cases hxt : x ∈ t
      · have hφx : φ x = z := htsub hxt
        rw [hx3 hxt, hφx]
      · rw [hx4 hxt, mul_zero, mul_zero]
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := u) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact hMu
    · intro hu0
      rw [hu0, norm_zero] at hu_norm
      exact zero_ne_one hu_norm

/-- `z` is an eigenvalue of the multiplication operator exactly when the level
set `{x | φ x = z}` has positive measure. -/
theorem hasEigenvalue_lpMulCLM_iff {φ : α → ℂ} (hφ : MemLp φ ∞ μ) (z : ℂ) :
    Module.End.HasEigenvalue (lpMulCLM φ hφ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) z ↔
      0 < μ {x | φ x = z} := by
  obtain ⟨ψ, hψmeas, hψae, hψ⟩ := exists_measurable_memLp hφ
  rw [lpMulCLM_congr_ae hψae hφ hψ]
  have hset : {x : α | φ x = z} =ᵐ[μ] {x : α | ψ x = z} := by
    filter_upwards [hψae] with x hx
    simp [hx]
  rw [MeasureTheory.measure_congr hset]
  exact hasEigenvalue_lpMulCLM_iff_of_measurable hψ hψmeas z

end MathlibExt.Analysis.FunctionalAnalysis.LpMultiplicationOperator

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Normed.Lp.DualC0

/-!
# Convolution of sequences on `ℤ`

For `f ∈ ℓ¹(ℤ, ℂ)` and `g ∈ ℓ^p(ℤ, ℂ)` the convolution
`(f * g) n = ∑' m, f m * g (n - m)` is again in `ℓ^p`, with
`‖f * g‖ ≤ ‖f‖ * ‖g‖`. On `ℓ¹` itself convolution is commutative and
associative, with unit the delta sequence at `0`: it makes `ℓ¹(ℤ, ℂ)` a
commutative Banach algebra, acting by bounded operators on every `ℓ^p`,
`1 ≤ p ≤ ∞`. This is the discrete form of Young's inequality with one
factor in `ℓ¹` (the case `1/p + 1/1 = 1 + 1/p`).

The proof writes the convolution as a sum of translates in the Banach space
`ℓ^p`, `f * g = ∑' m, f m • shift m g`, where `shift m` is translation by
`m`; absolute summability of the terms is the coordinate bound
`‖g (n - m)‖ ≤ ‖g‖` together with `∑' m, ‖f m‖ = ‖f‖`. Associativity is
proved by interchanging two absolutely convergent double sums.

Companion to the `L^p`/Hölder/Minkowski and Fourier material of
`IntroductionToFunctionalAnalysis` (v1); not one of the book's 72 formalized
targets. Mathlib has convolution for functions on locally compact groups via
the Bochner integral, but no pointwise `ℓ¹(ℤ) × ℓ^p(ℤ) → ℓ^p(ℤ)` convolution,
no `ℓ¹(ℤ)` algebra laws, and no `ℓ¹` action on `ℓ^p`.

## Main declarations

* `intConv` : pointwise convolution of two functions `ℤ → ℂ`, as a series.
* `l1Conv` : convolution of an `ℓ¹` sequence with an `ℓ^p` sequence.
* `l1Conv_apply` : `(l1Conv f g) n = ∑' m, f m * g (n - m)`.
* `norm_l1Conv_le` : `‖l1Conv f g‖ ≤ ‖f‖ * ‖g‖`.
* `l1ConvCLM` : the action as a bounded linear map
  `ℓ¹(ℤ, ℂ) →L[ℂ] (ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^p(ℤ, ℂ))`, with `‖l1ConvCLM‖ ≤ 1`.
* `l1Conv_comm` / `l1Conv_assoc` : commutativity and associativity on `ℓ¹`.
* `l1Delta` / `l1Conv_delta_left` / `l1Conv_delta_right` : the unit sequence.
* `l1Conv_single_single` : convolution of two coordinate vectors.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.IntConvolution

open Filter Topology
open scoped ENNReal lp

/-- The exponent `1` in `ℝ≥0∞` is nonzero. -/
private theorem one_ne_zero_ennreal : (1 : ℝ≥0∞) ≠ 0 := by norm_num

/-- A `Fact (1 ≤ p)` hypothesis implies `p ≠ 0`. -/
private theorem ne_zero_of_fact {p : ℝ≥0∞} [Fact (1 ≤ p)] : p ≠ 0 :=
  zero_lt_one.trans_le Fact.out |>.ne'

/-- Convolution of two complex sequences on `ℤ`, as a series. The series is
`0` when it does not converge; for `f ∈ ℓ¹` and `g ∈ ℓ^p` it always
converges (see `summable_intConv_term`). -/
noncomputable def intConv (f g : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑' m, f m * g (n - m)

/-- The `ℓ¹` norm is the sum of the coordinate norms. -/
theorem tsum_norm_l1 (f : ℓ¹(ℤ, ℂ)) : ∑' m, ‖(f : ℤ → ℂ) m‖ = ‖f‖ := by
  have h : ‖f‖
      = (∑' m, ‖(f : ℤ → ℂ) m‖ ^ (1 : ℝ≥0∞).toReal) ^ (1 / (1 : ℝ≥0∞).toReal) :=
    lp.norm_eq_tsum_rpow (by simp) f
  rw [ENNReal.toReal_one] at h
  simpa using h.symm

/-- The terms of a convolution of an `ℓ¹` sequence with an `ℓ^p` sequence are
summable. -/
theorem summable_intConv_term {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) (n : ℤ) :
    Summable fun m => (f : ℤ → ℂ) m * g (n - m) := by
  refine Summable.of_norm_bounded
    ((MathlibExt.Analysis.Normed.Lp.DualC0.summable_norm_lp_one f).mul_right ‖g‖)
    (fun m => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm ne_zero_of_fact g (n - m)) (norm_nonneg _)

/-- Translating an `ℓ^p` sequence on `ℤ` preserves `ℓ^p` membership. -/
theorem memℓp_shift {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : ℤ → ℂ} (hg : Memℓp g p)
    (m : ℤ) : Memℓp (fun n => g (n - m)) p := by
  rcases eq_or_ne p ⊤ with rfl | hpT
  · rw [memℓp_infty_iff]
    obtain ⟨C, hC⟩ := hg.bddAbove
    refine ⟨C, ?_⟩
    rintro x ⟨n, rfl⟩
    exact hC ⟨n - m, rfl⟩
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos ne_zero_of_fact hpT
    rw [memℓp_gen_iff hp0]
    have h := hg.summable hp0
    have h2 := ((Equiv.subRight m).hasSum_iff (f := fun k => ‖g k‖ ^ p.toReal)
      (a := ∑' k, ‖g k‖ ^ p.toReal)).mpr h.hasSum
    simpa [Function.comp_def, Equiv.subRight_apply] using h2.summable

/-- Translation of an `ℓ^p` sequence on `ℤ` by `m`. -/
noncomputable def shiftLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (m : ℤ)
    (g : ℓ^p(ℤ, ℂ)) : ℓ^p(ℤ, ℂ) :=
  ⟨fun n => g (n - m), memℓp_shift g.2 m⟩

/-- Pointwise action of a translation. -/
theorem shiftLp_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] (m : ℤ) (g : ℓ^p(ℤ, ℂ))
    (n : ℤ) : shiftLp m g n = g (n - m) :=
  rfl

/-- Translation is an isometry of `ℓ^p(ℤ, ℂ)`. -/
theorem norm_shiftLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (m : ℤ)
    (g : ℓ^p(ℤ, ℂ)) : ‖shiftLp m g‖ = ‖g‖ := by
  rcases eq_or_ne p ⊤ with rfl | hpT
  · rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
    have h := (Equiv.subRight m).iSup_comp (g := fun k => ‖(g : ℤ → ℂ) k‖)
    simpa [Equiv.subRight_apply, shiftLp_apply] using h
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos ne_zero_of_fact hpT
    rw [lp.norm_eq_tsum_rpow hp0, lp.norm_eq_tsum_rpow hp0]
    congr 1
    have h := (Equiv.subRight m).tsum_eq (fun k => ‖(g : ℤ → ℂ) k‖ ^ p.toReal)
    simpa [Equiv.subRight_apply, shiftLp_apply] using h

/-- The terms of the Banach-space series defining `l1Conv` are summable. -/
theorem summable_l1Conv_term {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) :
    Summable fun m => (f : ℤ → ℂ) m • shiftLp m g := by
  refine Summable.of_norm_bounded
    ((MathlibExt.Analysis.Normed.Lp.DualC0.summable_norm_lp_one f).mul_right ‖g‖)
    (fun m => ?_)
  rw [norm_smul, norm_shiftLp]

/-- Convolution of an `ℓ¹` sequence with an `ℓ^p` sequence, as an element of
`ℓ^p(ℤ, ℂ)`: the Banach-space sum `∑' m, f m • shift m g`. -/
noncomputable def l1Conv {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) : ℓ^p(ℤ, ℂ) :=
  ∑' m : ℤ, (f : ℤ → ℂ) m • shiftLp m g

/-- Pointwise formula for convolution. -/
theorem l1Conv_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) (n : ℤ) :
    l1Conv f g n = intConv (f : ℤ → ℂ) (g : ℤ → ℂ) n := by
  show (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n) (l1Conv f g)
    = ∑' m, (f : ℤ → ℂ) m * g (n - m)
  unfold l1Conv
  rw [(lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).map_tsum (summable_l1Conv_term f g)]
  apply tsum_congr
  intro m
  show ((f : ℤ → ℂ) m • shiftLp m g) n = (f : ℤ → ℂ) m * g (n - m)
  rw [show ((f : ℤ → ℂ) m • shiftLp m g) n
      = (f : ℤ → ℂ) m * (shiftLp m g) n from rfl, shiftLp_apply]

/-- Young's inequality for convolution with one `ℓ¹` factor. -/
theorem norm_l1Conv_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) :
    ‖l1Conv f g‖ ≤ ‖f‖ * ‖g‖ := by
  have hsum : Summable fun m => ‖(f : ℤ → ℂ) m • shiftLp m g‖ := by
    refine Summable.of_norm_bounded
      ((MathlibExt.Analysis.Normed.Lp.DualC0.summable_norm_lp_one f).mul_right ‖g‖)
      (fun m => ?_)
    rw [norm_smul, norm_shiftLp, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc ‖l1Conv f g‖
      = ‖∑' m, (f : ℤ → ℂ) m • shiftLp m g‖ := rfl
    _ ≤ ∑' m, ‖(f : ℤ → ℂ) m • shiftLp m g‖ := norm_tsum_le_tsum_norm hsum
    _ = ∑' m, ‖(f : ℤ → ℂ) m‖ * ‖g‖ := by
        apply tsum_congr
        intro m
        rw [norm_smul, norm_shiftLp]
    _ = (∑' m, ‖(f : ℤ → ℂ) m‖) * ‖g‖ := tsum_mul_right
    _ = ‖f‖ * ‖g‖ := by rw [tsum_norm_l1 f]

/-- Convolution is additive in the `ℓ¹` argument. -/
theorem l1Conv_add_left {p : ℝ≥0∞} [Fact (1 ≤ p)] (f₁ f₂ : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) :
    l1Conv (f₁ + f₂) g = l1Conv f₁ g + l1Conv f₂ g := by
  apply lp.ext
  funext n
  show l1Conv (f₁ + f₂) g n = (l1Conv f₁ g) n + (l1Conv f₂ g) n
  rw [l1Conv_apply, l1Conv_apply, l1Conv_apply]
  show (∑' m, ((f₁ + f₂ : ℓ¹(ℤ, ℂ)) : ℤ → ℂ) m * g (n - m))
      = (∑' m, (f₁ : ℤ → ℂ) m * g (n - m))
        + ∑' m, (f₂ : ℤ → ℂ) m * g (n - m)
  rw [← (summable_intConv_term f₁ g n).tsum_add (summable_intConv_term f₂ g n)]
  apply tsum_congr
  intro m
  show ((f₁ : ℤ → ℂ) m + (f₂ : ℤ → ℂ) m) * g (n - m)
      = (f₁ : ℤ → ℂ) m * g (n - m) + (f₂ : ℤ → ℂ) m * g (n - m)
  rw [add_mul]

/-- Convolution is additive in the `ℓ^p` argument. -/
theorem l1Conv_add_right {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ))
    (g₁ g₂ : ℓ^p(ℤ, ℂ)) :
    l1Conv f (g₁ + g₂) = l1Conv f g₁ + l1Conv f g₂ := by
  apply lp.ext
  funext n
  show l1Conv f (g₁ + g₂) n = (l1Conv f g₁) n + (l1Conv f g₂) n
  rw [l1Conv_apply, l1Conv_apply, l1Conv_apply]
  show (∑' m, (f : ℤ → ℂ) m * ((g₁ + g₂ : ℓ^p(ℤ, ℂ)) : ℤ → ℂ) (n - m))
      = (∑' m, (f : ℤ → ℂ) m * g₁ (n - m))
        + ∑' m, (f : ℤ → ℂ) m * g₂ (n - m)
  rw [← (summable_intConv_term f g₁ n).tsum_add (summable_intConv_term f g₂ n)]
  apply tsum_congr
  intro m
  show (f : ℤ → ℂ) m * ((g₁ : ℤ → ℂ) (n - m) + (g₂ : ℤ → ℂ) (n - m))
      = (f : ℤ → ℂ) m * g₁ (n - m) + (f : ℤ → ℂ) m * g₂ (n - m)
  rw [mul_add]

/-- Convolution commutes with scalar multiplication in the `ℓ¹` argument. -/
theorem l1Conv_smul_left {p : ℝ≥0∞} [Fact (1 ≤ p)] (c : ℂ) (f : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) :
    l1Conv (c • f) g = c • l1Conv f g := by
  apply lp.ext
  funext n
  show l1Conv (c • f) g n = c * (l1Conv f g) n
  rw [l1Conv_apply, l1Conv_apply]
  show (∑' m, ((c • f : ℓ¹(ℤ, ℂ)) : ℤ → ℂ) m * g (n - m))
      = c * ∑' m, (f : ℤ → ℂ) m * g (n - m)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  show (c * (f : ℤ → ℂ) m) * g (n - m) = c * ((f : ℤ → ℂ) m * g (n - m))
  rw [mul_assoc]

/-- Convolution commutes with scalar multiplication in the `ℓ^p` argument. -/
theorem l1Conv_smul_right {p : ℝ≥0∞} [Fact (1 ≤ p)] (c : ℂ) (f : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) :
    l1Conv f (c • g) = c • l1Conv f g := by
  apply lp.ext
  funext n
  show l1Conv f (c • g) n = c * (l1Conv f g) n
  rw [l1Conv_apply, l1Conv_apply]
  show (∑' m, (f : ℤ → ℂ) m * ((c • g : ℓ^p(ℤ, ℂ)) : ℤ → ℂ) (n - m))
      = c * ∑' m, (f : ℤ → ℂ) m * g (n - m)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  show (f : ℤ → ℂ) m * (c * g (n - m)) = c * ((f : ℤ → ℂ) m * g (n - m))
  rw [mul_left_comm]

/-- Convolution with `0` on the left is `0`. -/
theorem l1Conv_zero_left {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : ℓ^p(ℤ, ℂ)) :
    l1Conv (p := p) 0 g = 0 := by
  apply lp.ext
  funext n
  rw [l1Conv_apply]
  show (∑' m, ((0 : ℓ¹(ℤ, ℂ)) : ℤ → ℂ) m * g (n - m)) = 0
  have h0 : ∀ m, ((0 : ℓ¹(ℤ, ℂ)) : ℤ → ℂ) m = 0 := fun _ => rfl
  simp only [h0, zero_mul, tsum_zero]

/-- Convolution with `0` on the right is `0`. -/
theorem l1Conv_zero_right {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ)) :
    l1Conv (p := p) f 0 = 0 := by
  apply lp.ext
  funext n
  rw [l1Conv_apply]
  show (∑' m, (f : ℤ → ℂ) m * ((0 : ℓ^p(ℤ, ℂ)) : ℤ → ℂ) (n - m)) = 0
  have h0 : ∀ m, ((0 : ℓ^p(ℤ, ℂ)) : ℤ → ℂ) m = 0 := fun _ => rfl
  simp only [h0, mul_zero, tsum_zero]

/-- For fixed `f ∈ ℓ¹`, convolution by `f` as a bounded operator on `ℓ^p`. -/
noncomputable def l1ConvCLMOf {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ)) :
    ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^p(ℤ, ℂ) :=
  ({ toFun := l1Conv f
     map_add' := fun g₁ g₂ => l1Conv_add_right f g₁ g₂
     map_smul' := fun c g => l1Conv_smul_right c f g } :
    ℓ^p(ℤ, ℂ) →ₗ[ℂ] ℓ^p(ℤ, ℂ)).mkContinuous ‖f‖ (fun g => norm_l1Conv_le f g)

/-- Pointwise action of the convolution operator. -/
theorem l1ConvCLMOf_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) : l1ConvCLMOf f g = l1Conv f g :=
  rfl

/-- The operator norm of convolution by `f` is at most `‖f‖`. -/
theorem norm_l1ConvCLMOf_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ)) :
    ‖l1ConvCLMOf (p := p) f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (fun g => norm_l1Conv_le f g)

/-- The convolution action as a bounded linear map
`ℓ¹(ℤ, ℂ) →L[ℂ] (ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^p(ℤ, ℂ))`. -/
noncomputable def l1ConvCLM {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    ℓ¹(ℤ, ℂ) →L[ℂ] (ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^p(ℤ, ℂ)) :=
  ({ toFun := l1ConvCLMOf
     map_add' := fun f₁ f₂ => by
        apply ContinuousLinearMap.ext
        intro g
        simp only [l1ConvCLMOf_apply, add_apply]
        exact l1Conv_add_left f₁ f₂ g
     map_smul' := fun c f => by
        apply ContinuousLinearMap.ext
        intro g
        simp only [l1ConvCLMOf_apply, smul_apply]
        exact l1Conv_smul_left c f g } :
    ℓ¹(ℤ, ℂ) →ₗ[ℂ] (ℓ^p(ℤ, ℂ) →L[ℂ] ℓ^p(ℤ, ℂ))).mkContinuous 1
    (fun f => by rw [one_mul]; exact norm_l1ConvCLMOf_le f)

/-- Pointwise action of the convolution action. -/
theorem l1ConvCLM_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℓ¹(ℤ, ℂ))
    (g : ℓ^p(ℤ, ℂ)) : l1ConvCLM f g = l1Conv f g :=
  rfl

/-- The convolution action has operator norm at most `1`. -/
theorem norm_l1ConvCLM_le {p : ℝ≥0∞} [Fact (1 ≤ p)] : ‖l1ConvCLM (p := p)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    rw [one_mul]; exact norm_l1ConvCLMOf_le f)

/-- Convolution of `ℓ¹` sequences is commutative. -/
theorem l1Conv_comm (f g : ℓ¹(ℤ, ℂ)) : l1Conv f g = l1Conv g f := by
  apply lp.ext
  funext n
  rw [l1Conv_apply, l1Conv_apply]
  simp only [intConv]
  calc ∑' m, (f : ℤ → ℂ) m * g (n - m)
      = ∑' a, (fun k => (f : ℤ → ℂ) (n - k) * g k) ((Equiv.subLeft n) a) := by
        apply tsum_congr
        intro a
        simp [Equiv.subLeft_apply, sub_sub_cancel]
    _ = ∑' k, (f : ℤ → ℂ) (n - k) * g k :=
        (Equiv.subLeft n).tsum_eq (fun k => (f : ℤ → ℂ) (n - k) * g k)
    _ = ∑' k, (g : ℤ → ℂ) k * f (n - k) := tsum_congr fun k => mul_comm _ _

/-- The shifted norm of an `ℓ¹` sequence, summed in the shift variable, equals
its norm: `∑' m, ‖h (n - m)‖ = ‖h‖`. -/
private theorem tsum_norm_sub_right (h : ℓ¹(ℤ, ℂ)) (n : ℤ) :
    (∑' m, ‖(h : ℤ → ℂ) (n - m)‖) = ‖h‖ := by
  have heq : (∑' a, ‖(h : ℤ → ℂ) (n - a)‖) = ∑' j, ‖(h : ℤ → ℂ) j‖ := by
    have hh := (Equiv.subLeft n).tsum_eq (fun j => ‖(h : ℤ → ℂ) j‖)
    simpa [Equiv.subLeft_apply] using hh
  rw [heq, tsum_norm_l1 h]

/-- Double-sum absolute summability used in the associativity proof: the
nonnegative triple product `‖f k‖ * ‖g (m - k)‖ * ‖h (n - m)‖` is summable
over `(k, m)`. -/
private theorem summable_double_norm (f g h : ℓ¹(ℤ, ℂ)) (n : ℤ) :
    Summable fun p : ℤ × ℤ =>
      ‖(f : ℤ → ℂ) p.1‖ * ‖g (p.2 - p.1)‖ * ‖(h : ℤ → ℂ) (n - p.2)‖ := by
  have hinner : ∀ k : ℤ,
      Summable fun m => ‖(f : ℤ → ℂ) k‖ * ‖g (m - k)‖ * ‖(h : ℤ → ℂ) (n - m)‖ := by
    intro k
    refine Summable.of_norm_bounded
      (g := fun m => ‖(f : ℤ → ℂ) k‖ * ‖g‖ * ‖(h : ℤ → ℂ) (n - m)‖) ?_ (fun m => ?_)
    · have hh : Summable fun m => ‖(h : ℤ → ℂ) (n - m)‖ := by
        have h2 := ((Equiv.subLeft n).hasSum_iff (f := fun j => ‖(h : ℤ → ℂ) j‖)
          (a := ∑' j, ‖(h : ℤ → ℂ) j‖)).mpr
          (MathlibExt.Analysis.Normed.Lp.DualC0.summable_norm_lp_one h).hasSum
        simpa [Function.comp_def, Equiv.subLeft_apply] using h2.summable
      exact hh.mul_left _
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm one_ne_zero_ennreal g (m - k)) (norm_nonneg _))
        (norm_nonneg _)
  have hinner_le : ∀ k : ℤ,
      (∑' m, ‖(f : ℤ → ℂ) k‖ * ‖g (m - k)‖ * ‖(h : ℤ → ℂ) (n - m)‖)
        ≤ ‖(f : ℤ → ℂ) k‖ * (‖g‖ * ‖h‖) := by
    intro k
    calc (∑' m, ‖(f : ℤ → ℂ) k‖ * ‖g (m - k)‖ * ‖(h : ℤ → ℂ) (n - m)‖)
        ≤ ∑' m, ‖(f : ℤ → ℂ) k‖ * ‖g‖ * ‖(h : ℤ → ℂ) (n - m)‖ := by
          apply Summable.tsum_le_tsum (fun m => ?_) (hinner k)
          · have hh : Summable fun m => ‖(f : ℤ → ℂ) k‖ * ‖g‖ * ‖(h : ℤ → ℂ) (n - m)‖ := by
              have h2 : Summable fun m => ‖(h : ℤ → ℂ) (n - m)‖ := by
                have h3 := ((Equiv.subLeft n).hasSum_iff
                  (f := fun j => ‖(h : ℤ → ℂ) j‖)
                  (a := ∑' j, ‖(h : ℤ → ℂ) j‖)).mpr
                  (MathlibExt.Analysis.Normed.Lp.DualC0.summable_norm_lp_one h).hasSum
                simpa [Function.comp_def, Equiv.subLeft_apply] using h3.summable
              exact h2.mul_left _
            exact hh
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (lp.norm_apply_le_norm one_ne_zero_ennreal g (m - k)) (norm_nonneg _))
              (norm_nonneg _)
      _ = (‖(f : ℤ → ℂ) k‖ * ‖g‖) * (∑' m, ‖(h : ℤ → ℂ) (n - m)‖) := by
          rw [tsum_mul_left]
      _ = ‖(f : ℤ → ℂ) k‖ * (‖g‖ * ‖h‖) := by
          rw [tsum_norm_sub_right h n, mul_assoc]
  rw [summable_prod_of_nonneg (fun p => by positivity)]
  refine ⟨fun k => hinner k, ?_⟩
  refine Summable.of_norm_bounded
    ((MathlibExt.Analysis.Normed.Lp.DualC0.summable_norm_lp_one f).mul_right (‖g‖ * ‖h‖))
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun m => by positivity)]
  exact hinner_le k

/-- Convolution of `ℓ¹` sequences is associative. -/
theorem l1Conv_assoc (f g h : ℓ¹(ℤ, ℂ)) : l1Conv (l1Conv f g) h = l1Conv f (l1Conv g h) := by
  apply lp.ext
  funext n
  have hL : (l1Conv (l1Conv f g) h) n
      = ∑' m, ∑' k, (f : ℤ → ℂ) k * g (m - k) * h (n - m) := by
    rw [l1Conv_apply]
    show (∑' m, (l1Conv f g : ℤ → ℂ) m * h (n - m))
      = ∑' m, ∑' k, (f : ℤ → ℂ) k * g (m - k) * h (n - m)
    apply tsum_congr
    intro m
    rw [l1Conv_apply]
    show (∑' x, (f : ℤ → ℂ) x * g (m - x)) * h (n - m)
      = ∑' k, (f : ℤ → ℂ) k * g (m - k) * h (n - m)
    rw [tsum_mul_right]
  have hR : (l1Conv f (l1Conv g h)) n
      = ∑' k, ∑' m, (f : ℤ → ℂ) k * (g (m - k) * h (n - m)) := by
    rw [l1Conv_apply]
    apply tsum_congr
    intro k
    have h1 : (l1Conv g h) (n - k) = ∑' j, (g : ℤ → ℂ) j * h (n - k - j) := by
      rw [l1Conv_apply]
      apply tsum_congr
      intro j
      rfl
    have hinner : (∑' j, (g : ℤ → ℂ) j * h (n - k - j))
        = ∑' m, (g : ℤ → ℂ) (m - k) * h (n - m) := by
      have h2 := (Equiv.addLeft k).tsum_eq
        (fun m => (g : ℤ → ℂ) (m - k) * h (n - m))
      rw [← h2]
      apply tsum_congr
      intro j
      show (g : ℤ → ℂ) j * h (n - k - j)
        = (g : ℤ → ℂ) (k + j - k) * h (n - (k + j))
      rw [add_sub_cancel_left, sub_add_eq_sub_sub]
    rw [h1, hinner, tsum_mul_left]
  rw [hL, hR]
  have h1 : (∑' k, ∑' m, (f : ℤ → ℂ) k * (g (m - k) * h (n - m)))
      = ∑' k, ∑' m, (f : ℤ → ℂ) k * g (m - k) * h (n - m) := by
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    rw [mul_assoc]
  rw [h1]
  have hsumNorm : Summable fun p : ℤ × ℤ =>
      ‖(f : ℤ → ℂ) p.2‖ * ‖g (p.1 - p.2)‖ * ‖(h : ℤ → ℂ) (n - p.1)‖ := by
    have h := summable_double_norm f g h n
    have h2 := (Equiv.prodComm ℤ ℤ).summable_iff.mpr h
    exact h2
  have hsum : Summable (Function.uncurry
      fun m k => (f : ℤ → ℂ) k * g (m - k) * h (n - m)) := by
    refine Summable.of_norm_bounded hsumNorm (fun p => ?_)
    show ‖(f : ℤ → ℂ) p.2 * g (p.1 - p.2) * h (n - p.1)‖
      ≤ ‖(f : ℤ → ℂ) p.2‖ * ‖g (p.1 - p.2)‖ * ‖(h : ℤ → ℂ) (n - p.1)‖
    rw [norm_mul, norm_mul]
  exact (Summable.tsum_comm hsum).symm

/-- The unit sequence `δ` at `0` in `ℓ¹(ℤ, ℂ)`. -/
noncomputable def l1Delta : ℓ¹(ℤ, ℂ) := lp.single (E := fun _ : ℤ => ℂ) 1 0 1

/-- Pointwise values of the unit sequence. -/
theorem l1Delta_apply (n : ℤ) : l1Delta n = if n = 0 then 1 else 0 := by
  by_cases h : n = 0
  · subst h
    have h2 : l1Delta 0 = 1 := lp.single_apply_self _ _ _
    rw [h2]
    simp
  · have h2 : l1Delta n = 0 := lp.single_apply_ne _ _ _ h
    rw [h2, ite_eq_right h]

/-- The norm of the unit sequence is `1`. -/
theorem norm_l1Delta : ‖l1Delta‖ = 1 := by
  rw [l1Delta, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  norm_num

/-- The unit sequence is a left unit for convolution. -/
theorem l1Conv_delta_left {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : ℓ^p(ℤ, ℂ)) :
    l1Conv l1Delta g = g := by
  apply lp.ext
  funext n
  rw [l1Conv_apply]
  show (∑' m, (l1Delta : ℤ → ℂ) m * g (n - m)) = g n
  rw [tsum_eq_single 0]
  · rw [l1Delta_apply]
    simp
  · intro m hm
    rw [l1Delta_apply, ite_eq_right hm, zero_mul]

/-- The unit sequence is a right unit for convolution on `ℓ¹`. -/
theorem l1Conv_delta_right (f : ℓ¹(ℤ, ℂ)) : l1Conv f l1Delta = f := by
  rw [l1Conv_comm f l1Delta, l1Conv_delta_left]

/-- Convolution of two coordinate vectors: positions add, coefficients
multiply. -/
theorem l1Conv_single_single {p : ℝ≥0∞} [Fact (1 ≤ p)] (i j : ℤ) (a b : ℂ) :
    l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 i a)
        (lp.single (E := fun _ : ℤ => ℂ) p j b)
      = lp.single (E := fun _ : ℤ => ℂ) p (i + j) (a * b) := by
  apply lp.ext
  funext n
  rw [l1Conv_apply]
  show (∑' m, (lp.single (E := fun _ : ℤ => ℂ) 1 i a : ℤ → ℂ) m
        * (lp.single (E := fun _ : ℤ => ℂ) p j b : ℤ → ℂ) (n - m))
      = (lp.single (E := fun _ : ℤ => ℂ) p (i + j) (a * b) : ℤ → ℂ) n
  rw [tsum_eq_single i]
  · by_cases hn : n = i + j
    · subst hn
      have e1 : (lp.single (E := fun _ : ℤ => ℂ) 1 i a) i = a :=
        lp.single_apply_self _ _ _
      have e2 : (lp.single (E := fun _ : ℤ => ℂ) p j b) (i + j - i) = b := by
        rw [add_sub_cancel_left]
        exact lp.single_apply_self _ _ _
      have e3 : (lp.single (E := fun _ : ℤ => ℂ) p (i + j) (a * b)) (i + j) = a * b :=
        lp.single_apply_self _ _ _
      rw [e1, e2, e3]
    · have h1 : n - i ≠ j := by
        intro hcon
        apply hn
        omega
      rw [lp.single_apply_ne _ _ _ h1, mul_zero]
      exact (lp.single_apply_ne (E := fun _ : ℤ => ℂ) p (i + j) (a * b) hn).symm
  · intro m hm
    rw [lp.single_apply_ne _ _ _ hm, zero_mul]

end MathlibExt.Analysis.FunctionalAnalysis.IntConvolution

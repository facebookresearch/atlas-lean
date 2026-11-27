/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import MathlibExt.Analysis.Convex.GradientDescent

@[expose] public section

/-! # Linear convergence of gradient descent

If `f` has an `L`-Lipschitz gradient (stated as the quadratic upper
bound) and is `μ`-strongly convex (the quadratic lower bound), with
`0 < μ ≤ L`, then gradient descent with step `1 / L` converges
linearly: `f (x_k) - f* ≤ (1 - μ / L)^k (f (x_0) - f*)`. The proof is
the descent lemma plus the Polyak-Łojasiewicz inequality obtained by
minimizing the strong-convexity quadratic. This file covers roadmap
package ML-19 of the Atlas TCS canon roadmap.

The same linear rate also holds under the Polyak-Łojasiewicz inequality
at a global minimizer, assumed directly (`gd_linear_rate_of_pl`), and for
the Mathlib gradient map `gradient f` with an `L`-Lipschitz gradient
(`gd_linear_rate_gradient_of_pl`).

Source: Nesterov, Introductory Lectures on Convex Optimization
(2004), Theorem 2.1.5 and Section 2.1.
-/

open scoped InnerProductSpace

/-- Gradient descent iterates for a function with gradient map `g`,
step size `1 / L`, starting from `x0`. -/
noncomputable def gdIter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (L : ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | k + 1 => gdIter g L x0 k - (L⁻¹ : ℝ) • g (gdIter g L x0 k)

private theorem gd_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : ∀ x y, f y ≤ f x + @inner ℝ E _ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
    (x : E) :
    f (x - (L⁻¹ : ℝ) • g x) ≤ f x - (1 / (2 * L)) * ‖g x‖ ^ 2 := by
  have hL : 0 < L := lt_of_lt_of_le hμ hμL
  have hLne : L ≠ 0 := ne_of_gt hL
  have h1 := hsmooth x (x - (L⁻¹ : ℝ) • g x)
  have hdiff : (x - (L⁻¹ : ℝ) • g x) - x = -((L⁻¹ : ℝ) • g x) := by abel
  rw [hdiff] at h1
  have hinner : @inner ℝ E _ (g x) (-((L⁻¹ : ℝ) • g x)) = -(L⁻¹) * ‖g x‖ ^ 2 := by
    rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hnorm : ‖-((L⁻¹ : ℝ) • g x)‖ ^ 2 = (L⁻¹) ^ 2 * ‖g x‖ ^ 2 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hinner, hnorm] at h1
  have h2Lne : (2 : ℝ) * L ≠ 0 := mul_ne_zero (by norm_num) hLne
  have heq : (-(L⁻¹) * ‖g x‖ ^ 2) + (L / 2) * ((L⁻¹) ^ 2 * ‖g x‖ ^ 2)
      = -(1 / (2 * L)) * ‖g x‖ ^ 2 := by
    field_simp
    ring
  have h1' : f (x - (L⁻¹ : ℝ) • g x)
      ≤ f x + ((-(L⁻¹) * ‖g x‖ ^ 2) + (L / 2) * ((L⁻¹) ^ 2 * ‖g x‖ ^ 2)) := by
    linarith [h1]
  rw [heq] at h1'
  linarith [h1']

private theorem gd_pl_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {μ : ℝ} (hμ : 0 < μ)
    (hstrong : ∀ x y, f x + @inner ℝ E _ (g x) (y - x) + (μ / 2) * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (x : E) :
    2 * μ * (f x - f xstar) ≤ ‖g x‖ ^ 2 := by
  have hsc := hstrong x xstar
  have hcs := real_inner_le_norm (g x) (x - xstar)
  have hflip : (xstar - x) = -(x - xstar) := by abel
  rw [hflip, inner_neg_right, norm_neg] at hsc
  have hstep1 : f x - f xstar ≤ ‖g x‖ * ‖x - xstar‖ - (μ / 2) * ‖x - xstar‖ ^ 2 := by
    linarith [hsc, hcs]
  have hstep2 : 2 * μ * (‖g x‖ * ‖x - xstar‖ - (μ / 2) * ‖x - xstar‖ ^ 2)
      ≤ ‖g x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖g x‖ - μ * ‖x - xstar‖)]
  have hμnn : (0 : ℝ) ≤ 2 * μ := by linarith [hμ]
  have hstep3 := mul_le_mul_of_nonneg_left hstep1 hμnn
  exact le_trans hstep3 hstep2

private theorem gd_onestep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : ∀ x y, f y ≤ f x + @inner ℝ E _ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
    (hstrong : ∀ x y, f x + @inner ℝ E _ (g x) (y - x) + (μ / 2) * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (x : E) :
    f (x - (L⁻¹ : ℝ) • g x) - f xstar ≤ (1 - μ / L) * (f x - f xstar) := by
  have hL : 0 < L := lt_of_lt_of_le hμ hμL
  have hLne : L ≠ 0 := ne_of_gt hL
  have hdesc := gd_descent hμ hμL hsmooth x
  have hpl := gd_pl_ineq hμ hstrong xstar x
  have hc : (0 : ℝ) ≤ 1 / (2 * L) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpl hc
  have h2Lne : (2 : ℝ) * L ≠ 0 := mul_ne_zero (by norm_num) hLne
  have heq : (1 / (2 * L)) * (2 * μ * (f x - f xstar))
      = (μ / L) * (f x - f xstar) := by
    field_simp
  rw [heq] at hmul
  have hrhs : (1 - μ / L) * (f x - f xstar)
      = (f x - f xstar) - (μ / L) * (f x - f xstar) := by ring
  rw [hrhs]
  have h1 : f (x - (L⁻¹ : ℝ) • g x) ≤ f x - (μ / L) * (f x - f xstar) := by
    linarith [hdesc, hmul]
  linarith [h1]

/-- Linear convergence of gradient descent: if `f` has an `L`-Lipschitz
gradient (the quadratic upper bound) and is `μ`-strongly convex (the
quadratic lower bound), with `0 < μ ≤ L`, then gradient descent with
step `1 / L` from any starting point converges linearly to the
minimizer `xstar` in function value. -/
theorem gd_linear_rate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : ∀ x y, f y ≤ f x + @inner ℝ E _ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
    (hstrong : ∀ x y, f x + @inner ℝ E _ (g x) (y - x) + (μ / 2) * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x0 : E) (k : ℕ) :
    f (gdIter g L x0 k) - f xstar ≤ (1 - μ / L) ^ k * (f x0 - f xstar) := by
  have _hm := hmin
  have hL : 0 < L := lt_of_lt_of_le hμ hμL
  have hρ : (0 : ℝ) ≤ 1 - μ / L := by
    have h1 : μ / L ≤ 1 := (div_le_one hL).mpr hμL
    linarith [h1]
  induction k with
  | zero => simp [gdIter]
  | succ k ih =>
    have hx : gdIter g L x0 (k + 1)
        = gdIter g L x0 k - (L⁻¹ : ℝ) • g (gdIter g L x0 k) := by
      simp [gdIter]
    rw [hx]
    have hstep := gd_onestep hμ hμL hsmooth hstrong xstar (gdIter g L x0 k)
    have hmul := mul_le_mul_of_nonneg_left ih hρ
    have hpow : (1 - μ / L) ^ (k + 1) * (f x0 - f xstar)
        = (1 - μ / L) * ((1 - μ / L) ^ k * (f x0 - f xstar)) := by
      rw [pow_succ]
      ring
    rw [hpow]
    exact le_trans hstep hmul

private theorem gd_onestep_of_pl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : ∀ x y, f y ≤ f x + @inner ℝ E _ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
    (xstar : E) (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖g x‖ ^ 2)
    (x : E) :
    f (x - (L⁻¹ : ℝ) • g x) - f xstar ≤ (1 - μ / L) * (f x - f xstar) := by
  have hL : 0 < L := lt_of_lt_of_le hμ hμL
  have hLne : L ≠ 0 := ne_of_gt hL
  have hdesc := gd_descent hμ hμL hsmooth x
  have hpl := hpl x
  have hc : (0 : ℝ) ≤ 1 / (2 * L) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpl hc
  have h2Lne : (2 : ℝ) * L ≠ 0 := mul_ne_zero (by norm_num) hLne
  have heq : (1 / (2 * L)) * (2 * μ * (f x - f xstar))
      = (μ / L) * (f x - f xstar) := by
    field_simp
  rw [heq] at hmul
  have hrhs : (1 - μ / L) * (f x - f xstar)
      = (f x - f xstar) - (μ / L) * (f x - f xstar) := by ring
  rw [hrhs]
  have h1 : f (x - (L⁻¹ : ℝ) • g x) ≤ f x - (μ / L) * (f x - f xstar) := by
    linarith [hdesc, hmul]
  linarith [h1]

/-- Linear convergence of gradient descent under the Polyak-Łojasiewicz
inequality at a global minimizer: with the quadratic upper bound and
`2 * μ * (f x - f xstar) ≤ ‖g x‖ ^ 2` for every `x`, where `xstar`
minimizes `f`, descent with step `1 / L` gives
`f (x_k) - f xstar ≤ (1 - μ / L)^k * (f (x_0) - f xstar)`. -/
theorem gd_linear_rate_of_pl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : ∀ x y, f y ≤ f x + @inner ℝ E _ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖g x‖ ^ 2)
    (x0 : E) (k : ℕ) :
    f (gdIter g L x0 k) - f xstar ≤ (1 - μ / L) ^ k * (f x0 - f xstar) := by
  have hL : 0 < L := lt_of_lt_of_le hμ hμL
  have hρ : (0 : ℝ) ≤ 1 - μ / L := by
    have h1 : μ / L ≤ 1 := (div_le_one hL).mpr hμL
    linarith [h1]
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ f (gdIter g L x0 n) - f xstar :=
    fun n => sub_nonneg.mpr (hmin (gdIter g L x0 n))
  induction k with
  | zero => simp [gdIter]
  | succ k ih =>
    have hx : gdIter g L x0 (k + 1)
        = gdIter g L x0 k - (L⁻¹ : ℝ) • g (gdIter g L x0 k) := by
      simp [gdIter]
    rw [hx]
    have hstep := gd_onestep_of_pl hμ hμL hsmooth xstar hpl (gdIter g L x0 k)
    have hmul := mul_le_mul_of_nonneg_left ih hρ
    have hpow : (1 - μ / L) ^ (k + 1) * (f x0 - f xstar)
        = (1 - μ / L) * ((1 - μ / L) ^ k * (f x0 - f xstar)) := by
      rw [pow_succ]
      ring
    rw [hpow]
    linarith [hstep, hmul, hnn k]

/-- Linear convergence of gradient descent for the Mathlib gradient map:
if `f` is differentiable with `L`-Lipschitz gradient and satisfies the
Polyak-Łojasiewicz inequality at a global minimizer `xstar`, then descent
with step `1 / L` converges linearly in function value. -/
theorem gd_linear_rate_gradient_of_pl {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith ⟨L, le_of_lt (lt_of_lt_of_le hμ hμL)⟩ (gradient f))
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
    (x0 : E) (k : ℕ) :
    f (gdIter (gradient f) L x0 k) - f xstar
      ≤ (1 - μ / L) ^ k * (f x0 - f xstar) := by
  have hL : 0 ≤ L := le_of_lt (lt_of_lt_of_le hμ hμL)
  have hquad : ∀ x y, f y ≤ f x + @inner ℝ E _ (gradient f x) (y - x)
      + (L / 2) * ‖y - x‖ ^ 2 := by
    intro x y
    have h := MetaMathlibExt.gradientDescent_descent_lemma hL hdiff hlip x (y - x)
    have hx : x + (y - x) = y := by abel
    rw [hx] at h
    exact h
  exact gd_linear_rate_of_pl hμ hμL hquad xstar hmin hpl x0 k

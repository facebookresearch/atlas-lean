/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.GradientDescent
public import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module

/-!
# Linear convergence of gradient descent for strongly convex functions

For an `m`-strongly convex function with `L`-Lipschitz gradient on a real Hilbert space, gradient
descent with a constant step `0 < η ≤ 1 / L` converges linearly:
`f(x_k) - p⋆ ≤ (1 - η m)^k (f(x_0) - p⋆)`, which for `η = 1 / L` is the rate `c = 1 - m / L` of
Boyd–Vandenberghe §9.3.1. The two ingredients are the first-order inequality of strong convexity
and its consequence `f(x) - p⋆ ≤ ‖∇f(x)‖² / (2m)` (Boyd–Vandenberghe eq. (9.9)), combined with
the sufficient decrease of a gradient step.

## Main results

* `add_inner_add_le_of_strongConvexOn`: `f x + ⟪∇f(x), y - x⟫ + m / 2 ‖y - x‖² ≤ f y`.
* `sub_le_norm_sq_div_of_strongConvexOn`: `f x - f y ≤ ‖∇f(x)‖² / (2m)` for all `y`.
* `le_of_strongConvexOn_of_lipschitzWith_gradient`: on a nontrivial space, `m ≤ L`.
* `gradient_descent_strongly_convex_linear_rate`: the linear rate.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.GradientDescentStronglyConvex

open MetaMathlibExt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem hasDerivAt_line {f : E → ℝ} {g x : E} (hg : HasGradientAt f g x) (d : E) :
    HasDerivAt (fun t : ℝ => f (x + t • d)) (inner ℝ g d) 0 := by
  have hpath : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hf : HasFDerivAt f (InnerProductSpace.toDual ℝ E g) (x + (0 : ℝ) • d) := by
    simpa using hg.hasFDerivAt
  simpa [Function.comp_def] using (hf.comp (0 : ℝ) hpath.hasFDerivAt).hasDerivAt

/-- **First-order condition for strong convexity.** If `f` is `m`-strongly convex on `s`,
`x, y ∈ s`, and `f` has gradient `g` at `x`, then
`f x + ⟪g, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§9.1.2, eq. (9.8); cf. Y. Nesterov, *Introductory Lectures on Convex Optimization*, Kluwer,
2004, Ch. 2 (strongly convex functions). -/
theorem add_inner_add_le_of_strongConvexOn {s : Set E} {m : ℝ} {f : E → ℝ} {g x y : E}
    (hf : StrongConvexOn s m f) (hx : x ∈ s) (hy : y ∈ s) (hg : HasGradientAt f g x) :
    f x + inner ℝ g (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hlim := (hasDerivAt_line hg (y - x)).tendsto_slope_zero_right
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hlim
  set K := m / 2 * ‖y - x‖ ^ 2 with hK
  have hrhs : Filter.Tendsto (fun t : ℝ => f y - f x - (1 - t) * K)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f y - f x - K)) := by
    have hc : Continuous (fun t : ℝ => f y - f x - (1 - t) * K) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      t⁻¹ * (f (x + t • (y - x)) - f x) ≤ f y - f x - (1 - t) * K := by
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hmem] with t ht
    have ht0 : 0 < t := ht.1
    have hconv := hf.2 hx hy (sub_nonneg.2 ht.2.le) ht0.le (by ring)
    have hpt : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [hpt, smul_eq_mul, smul_eq_mul, norm_sub_rev x y] at hconv
    rw [inv_mul_le_iff₀ ht0]
    have : t * (f y - f x - (1 - t) * K) = t * f y + (1 - t) * f x - f x - (1 - t) * t * K := by
      ring
    rw [this, hK]
    linarith
  have := le_of_tendsto_of_tendsto hlim hrhs hev
  linarith

/-- **Suboptimality bound from strong convexity.** If `f` is `m`-strongly convex on the whole
space with `m > 0` and has gradient `g` at `x`, then `f x - f y ≤ ‖g‖ ^ 2 / (2 m)` for every `y`;
in particular `f x - p⋆ ≤ ‖∇f(x)‖ ^ 2 / (2 m)`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§9.1.2, eq. (9.9). -/
theorem sub_le_norm_sq_div_of_strongConvexOn {m : ℝ} {f : E → ℝ} {g x : E} (hm : 0 < m)
    (hf : StrongConvexOn Set.univ m f) (hg : HasGradientAt f g x) (y : E) :
    f x - f y ≤ ‖g‖ ^ 2 / (2 * m) := by
  have h1 := add_inner_add_le_of_strongConvexOn hf (Set.mem_univ x) (Set.mem_univ y) hg
  have h0 : 0 ≤ ‖g + m • (y - x)‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hm,
    mul_pow] at h0
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h1, h0, hm]


/-- **Strong convexity modulus is at most the smoothness constant.** On a nontrivial real
Hilbert space, an `m`-strongly convex differentiable function with `L`-Lipschitz gradient has
`m ≤ L`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§9.1.2 (`m I ⪯ ∇²f ⪯ M I`, so `m ≤ M`; the ratio `M / m` bounds the condition number). -/
theorem le_of_strongConvexOn_of_lipschitzWith_gradient [Nontrivial E] {m L : ℝ} {f : E → ℝ}
    (hL : 0 ≤ L) (hf : StrongConvexOn Set.univ m f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, hL⟩ (gradient f)) : m ≤ L := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have h1 := add_inner_add_le_of_strongConvexOn hf (Set.mem_univ 0) (Set.mem_univ v)
    (hdiff 0).hasGradientAt
  have h2 := gradientDescent_descent_lemma hL hdiff hsmooth 0 v
  simp only [sub_zero, zero_add] at h1 h2
  have hpos : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith

/-- **Linear convergence of gradient descent for strongly convex functions.** Let `f` be
differentiable on a real Hilbert space, `m`-strongly convex with `m > 0`, with `L`-Lipschitz
gradient (`L > 0`), and let `0 < η ≤ 1 / L`. If `x_{k+1} = x_k - η ∇f(x_k)` for all `k`, then
for every point `x⋆` (in particular a minimizer) and every `k`,
`f(x_k) - f(x⋆) ≤ (1 - η m)^k (f(x_0) - f(x⋆))`, where `0 ≤ 1 - η m < 1` on a nontrivial
space. For `η = 1 / L` this is the rate `c = 1 - m / L`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§9.3.1, eq. (9.18) and the analysis there (`f(x⁺) ≤ f(x) - ‖∇f(x)‖² / (2M)` combined with
eq. (9.9)); cf. Y. Nesterov, *Introductory Lectures on Convex Optimization*, Kluwer, 2004,
Ch. 2 (the gradient method on smooth strongly convex functions). -/
theorem gradient_descent_strongly_convex_linear_rate {m L : ℝ} {f : E → ℝ} (hL : 0 < L)
    (hm : 0 < m) (hf : StrongConvexOn Set.univ m f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, hL.le⟩ (gradient f)) {η : ℝ} (hη : η ∈ Set.Ioc 0 (1 / L))
    {X : ℕ → E} (hX : ∀ k, X (k + 1) = X k - η • gradient f (X k)) (xstar : E) :
    ∀ k : ℕ, f (X k) - f xstar ≤ (1 - η * m) ^ k * (f (X 0) - f xstar) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · intro k
    have : X k = X 0 := Subsingleton.elim _ _
    have h' : X 0 = xstar := Subsingleton.elim _ _
    simp [this, h']
  have hmL := le_of_strongConvexOn_of_lipschitzWith_gradient hL.le hf hdiff hsmooth
  have hηm : η * m ≤ 1 := by
    have h1 : η * m ≤ (1 / L) * m := mul_le_mul_of_nonneg_right hη.2 hm.le
    have h2 : (1 / L) * m ≤ 1 := by rw [one_div_mul_eq_div, div_le_one hL]; exact hmL
    linarith
  have hstep : ∀ k, f (X (k + 1)) - f xstar ≤ (1 - η * m) * (f (X k) - f xstar) := by
    intro k
    have hdec := gradientDescent_sufficient_decrease hL hdiff hsmooth hη (X k)
    rw [← hX k] at hdec
    have hpl := sub_le_norm_sq_div_of_strongConvexOn hm hf (hdiff (X k)).hasGradientAt xstar
    rw [le_div_iff₀ (by positivity)] at hpl
    have hη0 : 0 ≤ η / 2 := by linarith [hη.1]
    nlinarith [mul_le_mul_of_nonneg_left hpl hη0]
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc f (X (k + 1)) - f xstar ≤ (1 - η * m) * (f (X k) - f xstar) := hstep k
      _ ≤ (1 - η * m) * ((1 - η * m) ^ k * (f (X 0) - f xstar)) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - η * m) ^ (k + 1) * (f (X 0) - f xstar) := by ring

end MathlibExt.Analysis.Convex.GradientDescentStronglyConvex

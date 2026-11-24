/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic.Positivity

/-!
# Quadratic convergence of Newton's method for minimization

For a twice differentiable function `f` whose Hessian `∇²f` is `L`-Lipschitz and satisfies
`∇²f(x) ⪰ m I` with `m > 0`, the pure Newton step `x⁺ = x + Δ`, `∇²f(x) Δ = -∇f(x)`, satisfies
`‖∇f(x⁺)‖ ≤ L / (2 m²) ‖∇f(x)‖²` (Boyd–Vandenberghe eq. (9.33)). Iterating, pure Newton steps
give `(L / (2 m²)) ‖∇f(xₖ)‖ ≤ ((L / (2 m²)) ‖∇f(x₀)‖)^(2^k)` (eq. (9.34) and the recursion after
it): once
`(L / (2 m²)) ‖∇f(x₀)‖ < 1`, the gradient converges to zero quadratically.

The Hessian is passed as a map `H : E → (E →L[ℝ] E)` with `HasFDerivAt (gradient f) (H y) y`; the
key estimate is the first-order Taylor bound `‖G (x + d) - G x - DG(x) d‖ ≤ L / 2 ‖d‖²` for a map
`G` with `L`-Lipschitz derivative (`norm_sub_sub_le_of_lipschitz_fderiv`).

## References

* S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, §9.5.3
  ("Quadratically convergent phase", eqs. (9.31), (9.33), (9.34)).
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.NewtonMinimization

/-- **Taylor remainder for a map with Lipschitz derivative.** If `G : E → F` has derivative
`DG(y)` at every `y` and `‖DG(y) - DG(y')‖ ≤ L ‖y - y'‖`, then
`‖G (x + d) - G x - DG(x) d‖ ≤ L / 2 * ‖d‖ ^ 2`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§9.5.3 (the integral estimate in the quadratically convergent phase, applied to `G = ∇f`);
cf. Y. Nesterov, *Introductory Lectures on Convex Optimization*, Kluwer, 2004, Ch. 1 (functions
with Lipschitz Hessian). -/
theorem norm_sub_sub_le_of_lipschitz_fderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {G : E → F}
    {DG : E → E →L[ℝ] F} {L : ℝ} (hG : ∀ y, HasFDerivAt G (DG y) y)
    (hL : ∀ y y', ‖DG y - DG y'‖ ≤ L * ‖y - y'‖) (x d : E) :
    ‖G (x + d) - G x - DG x d‖ ≤ L / 2 * ‖d‖ ^ 2 := by
  set ψ : ℝ → F := fun t => G (x + t • d) - G x - t • DG x d with hψ
  have hpath (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hψd (t : ℝ) : HasDerivAt ψ (DG (x + t • d) d - DG x d) t := by
    have h1 : HasDerivAt (fun s : ℝ => G (x + s • d)) (DG (x + t • d) d) t := by
      simpa [Function.comp_def] using ((hG (x + t • d)).comp t (hpath t).hasFDerivAt).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s • DG x d) (DG x d) t := by
      simpa using (hasDerivAt_id t).smul_const (DG x d)
    exact (h1.sub_const (G x)).sub h2
  set B : ℝ → ℝ := fun t => L / 2 * t ^ 2 * ‖d‖ ^ 2 with hB
  have hBd (t : ℝ) : HasDerivAt B (L * t * ‖d‖ ^ 2) t := by
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have := (hsq.const_mul (L / 2)).mul_const (‖d‖ ^ 2)
    convert this using 1
    ring
  have hψ0 : ‖ψ 0‖ ≤ B 0 := by simp [hψ, hB]
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖DG (x + t • d) d - DG x d‖ ≤ L * t * ‖d‖ ^ 2 := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    calc ‖DG (x + t • d) d - DG x d‖ = ‖(DG (x + t • d) - DG x) d‖ := by
          simp
      _ ≤ ‖DG (x + t • d) - DG x‖ * ‖d‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * ‖x + t • d - x‖) * ‖d‖ := mul_le_mul_of_nonneg_right (hL _ _) (norm_nonneg d)
      _ = L * t * ‖d‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
          ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := ψ) (f' := fun t => DG (x + t • d) d - DG x d) (a := 0) (b := 1)
    (fun t _ => (hψd t).continuousAt.continuousWithinAt)
    (fun t _ => (hψd t).hasDerivWithinAt) hψ0 hBd hbound
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa [hψ, hB] using key

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **One pure Newton step squares the gradient norm.** Let `f` have gradient `∇f` with derivative
(Hessian) `H y` at every `y`, with `‖H y - H y'‖ ≤ L ‖y - y'‖` (`L ≥ 0`), and suppose
`m ‖v‖² ≤ ⟪H x v, v⟫` for all `v`, with `m > 0`. If the Newton step `Δ` solves
`H x Δ = -∇f(x)`, then `‖∇f(x + Δ)‖ ≤ L / (2 m²) * ‖∇f(x)‖²`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§9.5.3, eq. (9.33) (only strong convexity at `x` is needed). -/
theorem norm_gradient_newton_step_le {f : E → ℝ} {H : E → E →L[ℝ] E} {L m : ℝ}
    (hL0 : 0 ≤ L) (hm : 0 < m) (hH : ∀ y, HasFDerivAt (gradient f) (H y) y)
    (hL : ∀ y y', ‖H y - H y'‖ ≤ L * ‖y - y'‖) {x Δ : E}
    (hstrong : ∀ v, m * ‖v‖ ^ 2 ≤ inner ℝ (H x v) v) (hΔ : H x Δ = -gradient f x) :
    ‖gradient f (x + Δ)‖ ≤ L / (2 * m ^ 2) * ‖gradient f x‖ ^ 2 := by
  set g := gradient f x with hg
  -- `‖Δ‖ ≤ ‖g‖ / m` from strong convexity at `x`.
  have hΔg : m * ‖Δ‖ ≤ ‖g‖ := by
    have h1 := hstrong Δ
    rw [hΔ, inner_neg_left] at h1
    have h2 : -inner ℝ g Δ ≤ ‖g‖ * ‖Δ‖ := by
      have := abs_real_inner_le_norm g Δ
      linarith [neg_abs_le (inner ℝ g Δ)]
    rcases (norm_nonneg Δ).lt_or_eq with hpos | hzero
    · have : m * ‖Δ‖ * ‖Δ‖ ≤ ‖g‖ * ‖Δ‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
    · rw [← hzero, mul_zero]; exact norm_nonneg g
  have htaylor := norm_sub_sub_le_of_lipschitz_fderiv hH hL x Δ
  rw [hΔ, ← hg, sub_neg_eq_add, sub_add_cancel] at htaylor
  have hΔle : ‖Δ‖ ≤ ‖g‖ / m := (le_div_iff₀ hm).2 (by linarith)
  have hsq : ‖Δ‖ ^ 2 ≤ (‖g‖ / m) ^ 2 := pow_le_pow_left₀ (norm_nonneg Δ) hΔle 2
  calc ‖gradient f (x + Δ)‖ ≤ L / 2 * ‖Δ‖ ^ 2 := htaylor
    _ ≤ L / 2 * (‖g‖ / m) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = L / (2 * m ^ 2) * ‖g‖ ^ 2 := by field_simp

/-- **Quadratic convergence of the pure Newton method.** Under the hypotheses of
`norm_gradient_newton_step_le`, with `m ‖v‖² ≤ ⟪H xₖ v, v⟫` at every iterate `xₖ`, if each iterate
is obtained by a pure Newton step, `H xₖ (xₖ₊₁ - xₖ) = -∇f(xₖ)`, then with `c = L / (2 m²)`,
`c ‖∇f(xₖ)‖ ≤ (c ‖∇f(x₀)‖)^(2^k)` for every `k`. In particular, if `c ‖∇f(x₀)‖ ≤ 1/2`, then
`c ‖∇f(xₖ)‖ ≤ (1/2)^(2^k)`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§9.5.3, eq. (9.34) and the recursion after it. -/
theorem newton_quadratic_convergence {f : E → ℝ} {H : E → E →L[ℝ] E} {L m : ℝ}
    (hL0 : 0 ≤ L) (hm : 0 < m) (hH : ∀ y, HasFDerivAt (gradient f) (H y) y)
    (hL : ∀ y y', ‖H y - H y'‖ ≤ L * ‖y - y'‖)
    {X : ℕ → E} (hstrong : ∀ k v, m * ‖v‖ ^ 2 ≤ inner ℝ (H (X k) v) v)
    (hX : ∀ k, H (X k) (X (k + 1) - X k) = -gradient f (X k)) :
    ∀ k : ℕ, L / (2 * m ^ 2) * ‖gradient f (X k)‖ ≤
      (L / (2 * m ^ 2) * ‖gradient f (X 0)‖) ^ (2 ^ k) := by
  set c := L / (2 * m ^ 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hstep : ∀ k, c * ‖gradient f (X (k + 1))‖ ≤ (c * ‖gradient f (X k)‖) ^ 2 := by
    intro k
    have h := norm_gradient_newton_step_le hL0 hm hH hL (hstrong k) (hX k)
    rw [add_sub_cancel] at h
    calc c * ‖gradient f (X (k + 1))‖ ≤ c * (c * ‖gradient f (X k)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h hc0
      _ = (c * ‖gradient f (X k)‖) ^ 2 := by ring
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc c * ‖gradient f (X (k + 1))‖ ≤ (c * ‖gradient f (X k)‖) ^ 2 := hstep k
      _ ≤ ((c * ‖gradient f (X 0)‖) ^ (2 ^ k)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hc0 (norm_nonneg _)) ih 2
      _ = (c * ‖gradient f (X 0)‖) ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]

end MathlibExt.Analysis.Convex.NewtonMinimization

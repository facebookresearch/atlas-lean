/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.GradientDescentLinearRate
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-- The first iterate is exactly one gradient step. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (L : ℝ) (x0 : E) :
    gdIter g L x0 1 = x0 - (L⁻¹ : ℝ) • g x0 := rfl

/-- Boundary check `k = 0`: the rate bound is the initial gap. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : ∀ x y, f y ≤ f x + @inner ℝ E _ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
    (hstrong : ∀ x y, f x + @inner ℝ E _ (g x) (y - x) + (μ / 2) * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x0 : E) :
    f (gdIter g L x0 0) - f xstar ≤ (1 - μ / L) ^ 0 * (f x0 - f xstar) :=
  gd_linear_rate hμ hμL hsmooth hstrong xstar hmin x0 0

/-- The quadratic `x²`, with gradient `2x`, has a nonzero contraction factor
when `μ = 2` and `L = 4`. The rate theorem bounds its second iterate. -/
example : (gdIter (fun x : ℝ => 2 * x) 4 2 2) ^ 2 ≤ 1 := by
  have hsmooth : ∀ x y : ℝ,
      y ^ 2 ≤ x ^ 2 + inner ℝ (2 * x) (y - x) + (4 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
    intro x y
    simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (y - x)]
  have hstrong : ∀ x y : ℝ,
      x ^ 2 + inner ℝ (2 * x) (y - x) + (2 / 2 : ℝ) * ‖y - x‖ ^ 2 ≤ y ^ 2 := by
    intro x y
    simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs]
    nlinarith
  have hmin : ∀ y : ℝ, (0 : ℝ) ^ 2 ≤ y ^ 2 := by
    intro y
    simpa using sq_nonneg y
  convert gd_linear_rate (f := fun x : ℝ => x ^ 2)
    (g := fun x : ℝ => 2 * x) (L := 4) (μ := 2) (by norm_num) (by norm_num)
    hsmooth hstrong 0 hmin 2 2 using 1 <;> norm_num

/-- The quadratic `x²`, with gradient `2x`, satisfies the
Polyak-Łojasiewicz inequality with `μ = 2`, so the PL rate theorem
bounds its second iterate when `L = 4`. -/
example : (gdIter (fun x : ℝ => 2 * x) 4 2 2) ^ 2 ≤ 1 := by
  have hsmooth : ∀ x y : ℝ,
      y ^ 2 ≤ x ^ 2 + inner ℝ (2 * x) (y - x) + (4 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
    intro x y
    simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (y - x)]
  have hpl : ∀ x : ℝ,
      2 * 2 * (x ^ 2 - (0 : ℝ) ^ 2) ≤ ‖(2 : ℝ) * x‖ ^ 2 := by
    intro x
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith
  have hmin : ∀ y : ℝ, (0 : ℝ) ^ 2 ≤ y ^ 2 := by
    intro y
    simpa using sq_nonneg y
  convert gd_linear_rate_of_pl (f := fun x : ℝ => x ^ 2)
    (g := fun x : ℝ => 2 * x) (L := 4) (μ := 2) (by norm_num) (by norm_num)
    hsmooth 0 hmin hpl 2 2 using 1 <;> norm_num

/-- The Mathlib-gradient bridge applies to any differentiable `f` with
`L`-Lipschitz gradient satisfying the PL inequality. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith ⟨L, le_of_lt (lt_of_lt_of_le hμ hμL)⟩ (gradient f))
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
    (x0 : E) (k : ℕ) :
    f (gdIter (gradient f) L x0 k) - f xstar
      ≤ (1 - μ / L) ^ k * (f x0 - f xstar) :=
  gd_linear_rate_gradient_of_pl hμ hμL hdiff hlip xstar hmin hpl x0 k

/-- The Mathlib gradient of the quadratic `x²` is `2x`, with
`4`-Lipschitz gradient and the PL inequality at `μ = 2`, so the
gradient bridge bounds its second iterate. -/
example : (gdIter (gradient fun x : ℝ => x ^ 2) 4 2 2) ^ 2 ≤ 1 := by
  have hgrad : gradient (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
    funext x
    rw [gradient_eq_deriv']
    have h := (hasDerivAt_pow 2 x).deriv
    rw [h]
    simp
  have hdiff : Differentiable ℝ fun x : ℝ => x ^ 2 :=
    fun x => (hasDerivAt_pow 2 x).differentiableAt
  have hlip : LipschitzWith ⟨4, by norm_num⟩ (gradient fun x : ℝ => x ^ 2) := by
    rw [hgrad]
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simp only [Real.dist_eq]
    change |2 * x - 2 * y| ≤ 4 * |x - y|
    have hxy : (2 : ℝ) * x - 2 * y = 2 * (x - y) := by ring
    rw [hxy, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
  have hpl : ∀ x : ℝ,
      2 * 2 * (x ^ 2 - (0 : ℝ) ^ 2) ≤ ‖gradient (fun x : ℝ => x ^ 2) x‖ ^ 2 := by
    rw [hgrad]
    intro x
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith
  have hmin : ∀ y : ℝ, (0 : ℝ) ^ 2 ≤ y ^ 2 := by
    intro y
    simpa using sq_nonneg y
  convert gd_linear_rate_gradient_of_pl (f := fun x : ℝ => x ^ 2)
    (L := 4) (μ := 2) (by norm_num) (by norm_num)
    hdiff hlip 0 hmin hpl 2 2 using 1 <;> norm_num

#print axioms gd_linear_rate_of_pl
#print axioms gd_linear_rate_gradient_of_pl

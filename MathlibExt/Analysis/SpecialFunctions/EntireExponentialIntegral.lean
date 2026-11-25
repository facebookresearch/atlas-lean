/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The entire exponential integral

This file defines

`Ein z = sum_(j >= 1) (-1)^(j+1) z^j / (j * j!)`

and proves its elementary analytic and derivative properties.
-/

@[expose] public section

namespace Complex

noncomputable section

open Set

/-- **Terms of the series for the entire exponential integral.** For a natural number $n$ and a
complex number $z$, this is the complex number $\frac{(-1)^n z^{n+1}}{(n+1) \cdot (n+1)!}$,
the term of index $j = n + 1$ in the series
$\operatorname{Ein}(z) = \sum_{j \ge 1} \frac{(-1)^{j+1} z^j}{j \cdot j!}$. -/
def einTerm (n : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * z ^ (n + 1) /
    (((n + 1 : ℕ) : ℂ) * ((n + 1).factorial : ℂ))

/-- **The entire exponential integral Ein.** The entire exponential integral is the function
$\operatorname{Ein} : \mathbb{C} \to \mathbb{C}$ defined by
$\operatorname{Ein}(z) = \sum_{j \ge 1} \frac{(-1)^{j+1} z^j}{j \cdot j!}$. -/
def ein (z : ℂ) : ℂ :=
  ∑' n : ℕ, einTerm n z

private theorem hasDerivAt_einTerm (n : ℕ) (z : ℂ) :
    HasDerivAt (einTerm n)
      ((-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z := by
  unfold einTerm
  have hne1 : ((n + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hneFac : (((n + 1).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h := (((hasDerivAt_const z ((-1 : ℂ) ^ n)).mul
    (hasDerivAt_pow (n + 1) z)).div_const
      (((n + 1 : ℕ) : ℂ) * ((n + 1).factorial : ℂ)))
  have hder : (0 * z ^ (n + 1) + (-1 : ℂ) ^ n * (((n + 1 : ℕ) : ℂ) * z ^ (n + 1 - 1))) /
        (((n + 1 : ℕ) : ℂ) * (((n + 1).factorial : ℕ) : ℂ)) =
      (-1 : ℂ) ^ n * z ^ n / (((n + 1).factorial : ℕ) : ℂ) := by
    rw [Nat.add_sub_cancel]
    simp only [zero_mul, zero_add]
    field_simp [hne1, hneFac]
  rwa [hder] at h

private theorem einTerm_deriv_norm_le {R : ℝ} {z : ℂ}
    (hz : ‖z‖ < R) (n : ℕ) :
    ‖(-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)‖ ≤
      R ^ n / n.factorial := by
  have hR : 0 ≤ R := le_trans (norm_nonneg z) hz.le
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_natCast, Nat.factorial_succ]
  gcongr
  rw [Nat.succ_mul, add_comm]
  exact Nat.le_add_right _ _

theorem hasDerivAt_ein (z : ℂ) :
    HasDerivAt ein
      (∑' n : ℕ,
        (-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z := by
  let R : ℝ := ‖z‖ + 1
  change HasDerivAt (fun w => ∑' n : ℕ, einTerm n w)
    (∑' n : ℕ,
      (-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => R ^ n / n.factorial)
    (g := einTerm)
    (g' := fun n w =>
      (-1 : ℂ) ^ n * w ^ n / ((n + 1).factorial : ℂ))
    (t := Metric.ball 0 R) (y₀ := 0) (y := z)
    (Real.summable_pow_div_factorial R)
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected ?_ ?_ ?_ ?_ ?_
  · intro n y _hy
    exact hasDerivAt_einTerm n y
  · intro n y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact einTerm_deriv_norm_le hy n
  · simp only [R, Metric.mem_ball, dist_zero_right, norm_zero]
    positivity
  · simp [einTerm]
  · simp [R, Metric.mem_ball]

/-- **Differentiability of the entire exponential integral.** The entire exponential integral
$\operatorname{Ein}$ is complex differentiable at every point of $\mathbb{C}$. -/
theorem differentiable_ein : Differentiable ℂ ein :=
  fun z => (hasDerivAt_ein z).differentiableAt

/-- **Analyticity of the entire exponential integral.** The entire exponential integral
$\operatorname{Ein}$ is complex analytic at every point of $\mathbb{C}$. -/
theorem analyticOnNhd_ein : AnalyticOnNhd ℂ ein univ :=
  analyticOnNhd_univ_iff_differentiable.mpr differentiable_ein

private theorem exp_tail (z : ℂ) :
    (∑' n : ℕ, (-z) ^ (n + 1) / ((n + 1).factorial : ℂ)) =
      Complex.exp (-z) - 1 := by
  have hfull : HasSum (fun n : ℕ => (-z) ^ n / (n.factorial : ℂ))
      (Complex.exp (-z)) := by
    simpa only [← Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (-z))
  simpa using ((hasSum_nat_add_iff' 1).mpr hfull).tsum_eq

/-- **Derivative of the entire exponential integral.** For every complex number $z$, the entire
exponential integral $\operatorname{Ein}$ satisfies $z \operatorname{Ein}'(z) = 1 - e^{-z}$.

This is the identity $\operatorname{Ein}'(z) = (1 - e^{-z})/z$ multiplied through by $z$, a form
that remains valid at $z = 0$. -/
theorem mul_deriv_ein (z : ℂ) :
    z * deriv ein z = 1 - Complex.exp (-z) := by
  rw [(hasDerivAt_ein z).deriv, ← tsum_mul_left]
  calc
    (∑' n : ℕ,
        z * ((-1 : ℂ) ^ n * z ^ n /
          ((n + 1).factorial : ℂ))) =
        ∑' n : ℕ,
          -((-z) ^ (n + 1) / ((n + 1).factorial : ℂ)) := by
      apply tsum_congr
      intro n
      have hneg : (-z) ^ n = (-1 : ℂ) ^ n * z ^ n :=
        neg_pow z n
      rw [pow_succ, hneg]
      ring
    _ = -(∑' n : ℕ,
          (-z) ^ (n + 1) / ((n + 1).factorial : ℂ)) := by
      rw [tsum_neg]
    _ = 1 - Complex.exp (-z) := by
      rw [exp_tail]
      ring

end

end Complex

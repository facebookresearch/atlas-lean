/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Farey staircases and harmonic blocks

The Farey staircase averages the lower rational approximations of a real number.
Harmonic blocks in its zoomed form can be compared with the integral of the reciprocal.
The dilation derivative of a differentiable function at `x` is `x * f' - f x`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Farey staircase.** For a natural number $n$ and a real number $x$, the Farey staircase of
order $n$ is $A_n(x) = \frac{1}{n} \sum_{k=1}^{n} \lfloor kx \rfloor / k$, the average of the
first $n$ lower rational approximations $\lfloor kx \rfloor / k$ of $x$. For $n = 0$ the sum is
empty and $A_0(x) = 0$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1, equation (2). -/
public noncomputable def fareyStaircase (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k

/-- **The Farey staircase of order zero vanishes.** For every real number $x$, the Farey staircase
$A_0$ of order $0$ satisfies $A_0(x) = 0$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1, equation (2). -/
public theorem fareyStaircase_zero (x : ℝ) : fareyStaircase 0 x = 0 := by
  simp [fareyStaircase]

/-- **The Farey staircase of order one is the floor function.** For every real number $x$, the
Farey staircase $A_1$ of order $1$ satisfies $A_1(x) = \lfloor x \rfloor$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1, equation (2). -/
public theorem fareyStaircase_one (x : ℝ) : fareyStaircase 1 x = ⌊x⌋ := by
  simp [fareyStaircase]

/-- **Recursion between consecutive Farey staircases.** Let $n \ge 2$ be a natural number and $x$
a real number, write $A_m$ for the Farey staircase of order $m$, and let
$D_n(x) = A_n(x) - A_{n-1}(x)$. Then
$D_n(x) = \frac{1}{n} \left( \lfloor nx \rfloor / n - A_{n-1}(x) \right)$ and
$D_n(x) = \frac{1}{n-1} \left( \lfloor nx \rfloor / n - A_n(x) \right)$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Proposition 7 (`integers-2024-A37-prop-7`). -/
public theorem fareyStaircase_sub_eq {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    fareyStaircase n x - fareyStaircase (n - 1) x =
        (n : ℝ)⁻¹ * (⌊(n : ℝ) * x⌋ / n - fareyStaircase (n - 1) x) ∧
      fareyStaircase n x - fareyStaircase (n - 1) x =
        ((n : ℝ) - 1)⁻¹ * (⌊(n : ℝ) * x⌋ / n - fareyStaircase n x) := by
  have hn₁ : 1 ≤ n := by omega
  have hn₀ : (n : ℝ) ≠ 0 := by positivity
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpred : (n : ℝ) - 1 ≠ 0 := by linarith
  have hsum : n * fareyStaircase n x =
      ((n : ℝ) - 1) * fareyStaircase (n - 1) x + ⌊(n : ℝ) * x⌋ / n := by
    simp only [fareyStaircase, Nat.cast_sub hn₁, Nat.cast_one, ← mul_assoc,
      mul_inv_cancel₀ hn₀, mul_inv_cancel₀ hpred, one_mul]
    simpa only [Nat.sub_add_cancel hn₁] using
      Finset.sum_Icc_succ_top (a := 1) (b := n - 1) (by omega)
        (fun k => (⌊(k : ℝ) * x⌋ : ℝ) / k)
  rw [eq_inv_mul_iff_mul_eq₀ hn₀, eq_inv_mul_iff_mul_eq₀ hpred]
  constructor <;> linear_combination hsum

/-- **Zoomed Farey staircase.** For a natural number $n$ and a real number $x$, the zoomed Farey
staircase of order $n$ is $B_0(x) = 0$ for $n = 0$ and $B_n(x) = n A_n(x/n)$ for $n \ge 1$, where
$A_n$ is the Farey staircase of order $n$. For $n \ge 1$ this equals
$\sum_{k=1}^{n} \lfloor (k/n) x \rfloor / k$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1.1, equation (4). -/
public noncomputable def fareyZoom (n : ℕ) (x : ℝ) : ℝ :=
  n * fareyStaircase n (x / n)

/-- **The zoomed Farey staircase as a sum.** For every natural number $n \ge 1$ and every real
number $x$, the zoomed Farey staircase $B_n$ of order $n$ satisfies
$B_n(x) = \sum_{k=1}^{n} \lfloor (k/n) x \rfloor / k$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1.1, equation (4). -/
public theorem fareyZoom_eq_sum {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    fareyZoom n x = ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) / n * x⌋ : ℝ) / k := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [fareyZoom, fareyStaircase, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_mul_eq_mul_div, mul_div_assoc]

/-- **The zoomed Farey staircase of order one is the floor function.** For every real number $x$,
the zoomed Farey staircase $B_1$ of order $1$ satisfies $B_1(x) = \lfloor x \rfloor$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1.1, equation (4). -/
public theorem fareyZoom_one (x : ℝ) : fareyZoom 1 x = ⌊x⌋ := by
  simp [fareyZoom, fareyStaircase_one]

/-- **Harmonic blocks versus the logarithmic integral.** Let $(a_n)$ and $(b_n)$ be sequences of
natural numbers with $a_n \le b_n$ for every $n$ and $a_n \to \infty$. Then
$\sum_{k=a_n}^{b_n} 1/k - \int_{a_n}^{b_n} dt/t \to 0$ as $n \to \infty$.

In particular, if either $\sum_{k=a_n}^{b_n} 1/k$ or $\int_{a_n}^{b_n} dt/t$ converges, then so does
the other, with the same limit. Positivity of $a_n$ and $b_n$ and $b_n \to \infty$ need not be
assumed: they follow from the hypotheses (positivity for all large $n$).

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 9 (`integers-2024-A37-lem-9`). -/
public theorem tendsto_harmonic_block_sub_integral {a b : ℕ → ℕ} (hab : ∀ n, a n ≤ b n)
    (ha : Filter.Tendsto a Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => ∑ k ∈ Finset.Icc (a n) (b n), (1 / k : ℝ) - ∫ t in (a n : ℝ)..(b n), t⁻¹)
      Filter.atTop (nhds 0) := by
  simp only [one_div]
  have hmono : ∀ᶠ n in Filter.atTop,
      AntitoneOn (fun x : ℝ => x⁻¹) (Set.Icc (a n : ℝ) (b n)) := by
    filter_upwards [ha.eventually_gt_atTop 0] with n hn
    exact antitoneOn_inv_pos.mono fun x hx => lt_of_lt_of_le (by exact_mod_cast hn) hx.1
  have hb := Filter.tendsto_atTop_mono hab ha
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hb).inv_tendsto_atTop
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp ha).inv_tendsto_atTop
  · filter_upwards [hmono] with n hn
    change (b n : ℝ)⁻¹ ≤ _
    rw [le_sub_iff_add_le, ← Finset.add_sum_Ico_eq_sum_Icc (hab n)]
    exact add_le_add_right (hn.integral_le_sum_Ico (hab n)) _
  · filter_upwards [hmono] with n hn
    change _ ≤ (a n : ℝ)⁻¹
    rw [sub_le_iff_le_add, ← Finset.add_sum_Ioc_eq_sum_Icc (hab n)]
    apply add_le_add_right
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, ← Finset.sum_Ico_add']
    exact hn.sum_le_integral_Ico (hab n)

/-- **Dilation derivative of a differentiable function.** Let $f : \mathbb{R} \to \mathbb{R}$ have
derivative $f'$ at the point $x \in \mathbb{R}$. Then the quotient
$(\lambda^{-1} f(\lambda x) - f(x))/(\lambda - 1)$ tends to $x f' - f(x)$ as $\lambda \to 1$ with
$\lambda \ne 1$; that is, the dilation derivative of $f$ at $x$ exists and equals $x f' - f(x)$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Proposition 12 (`integers-2024-A37-prop-12`); dilation derivative as defined
before it. -/
public theorem tendsto_dilation_quotient {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    Filter.Tendsto (fun l : ℝ => (l⁻¹ * f (l * x) - f x) / (l - 1)) (nhdsWithin 1 {1}ᶜ)
      (nhds (x * f' - f x)) := by
  have hcomp : HasDerivAt (fun l : ℝ => f (l * x)) (f' * x) 1 :=
    hf.comp_of_eq 1 (hasDerivAt_mul_const x) (one_mul x).symm
  simpa [slope_fun_def_field, div_eq_inv_mul, mul_comm f' x] using
    (hcomp.fun_div (hasDerivAt_id' 1) one_ne_zero).tendsto_slope

end

end MetaMathlibExt

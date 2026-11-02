/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Farey staircases

Statements from David Harry Richman, *Lower Rational Approximations and Farey Staircases*,
INTEGERS 24 (2024), Article A37 (primary text: arXiv:2303.02935).

The Farey staircase `A_n(x) = (1/n) Σ_{k=1}^n ⌊kx⌋/k` averages the lower rational approximations
`⌊kx⌋/k`; `B_n(x) = n A_n(x/n)` zooms in at the origin; `D_n = A_n - A_{n-1}`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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

/-- **Limit of the Farey staircase zoomed at the origin.** Let $B_n$ be the zoomed Farey staircase
of order $n$. For every real $x \ge 0$, $B_n(x) \to \sum_{k=1}^{\lfloor x \rfloor} \log(x/k)$ as
$n \to \infty$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 1 (`integers-2024-A37-thm-1`). -/
public theorem_wanted tendsto_fareyZoom {x : ℝ} (hx : 0 ≤ x) :
    Filter.Tendsto (fun n : ℕ => fareyZoom n x) Filter.atTop
      (nhds (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k)))

/-- **Limit of the Farey staircase zoomed at a rational point.** Let $B_n$ be the zoomed Farey
staircase of order $n$, let $x \ge 0$ be real, and let $p$ and $q$ be coprime positive integers.
Then $B_n(x + pn/q) - B_n(pn/q) \to \frac{1}{q} \sum_{k=1}^{\lfloor qx \rfloor} \log(qx/k)$ as
$n \to \infty$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 3 (`integers-2024-A37-thm-3`). -/
public theorem_wanted tendsto_fareyZoom_sub_at_rational {x : ℝ} (hx : 0 ≤ x) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q) :
    Filter.Tendsto
      (fun n : ℕ => fareyZoom n (x + (p : ℝ) / q * n) - fareyZoom n ((p : ℝ) / q * n))
      Filter.atTop
      (nhds ((q : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 ⌊(q : ℝ) * x⌋₊, Real.log (q * x / k)))

/-- **Limit of the rescaled Farey staircase increment.** Let $A_n$ be the Farey staircase of order
$n$ and $D_n = A_n - A_{n-1}$. For every real $x \ge 0$,
$n^2 D_n(x/n) \to \sum_{k=1}^{\lfloor x \rfloor} (1 - \log(x/k))$ as $n \to \infty$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 4 (`integers-2024-A37-thm-4`). -/
public theorem_wanted tendsto_sq_mul_fareyStaircase_sub {x : ℝ} (hx : 0 ≤ x) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ 2 * (fareyStaircase n (x / n) - fareyStaircase (n - 1) (x / n)))
      Filter.atTop (nhds (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 - Real.log (x / k))))

/-- **Floor gaps of Farey staircases are dense above $1 - \log 2$.** For $n \ge 1$ and
$x \in \mathbb{R}$ let $f_n(x) = \lfloor nx \rfloor - n A_n(x)$, where $A_n$ is the Farey staircase
of order $n$; thus $f_n(x) = \lfloor nx \rfloor - \sum_{k=1}^n \lfloor kx \rfloor / k$. Every real
number $y \ge 1 - \log 2$ lies in the closure of the set
$S = \{f_n(x) : n \ge 1,\ x \in \mathbb{R}\}$, that is, $S$ is dense in $[1 - \log 2, \infty)$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 5 (i) (`integers-2024-A37-thm-5`), also Corollary 6
(`integers-2024-A37-cor-6`). -/
public theorem_wanted Ici_one_sub_log_two_subset_closure_floor_gaps :
    Set.Ici (1 - Real.log 2) ⊆
      closure {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ, y = ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x}

/-- **Finiteness of small floor gaps of the Farey staircase.** For a natural number $n \ge 1$ and a
real number $x$, let $f_n(x) = \lfloor nx \rfloor - n A_n(x)$, where $A_n$ is the Farey staircase
of order $n$. Then for every real number $\varepsilon > 0$, only finitely many distinct real
numbers that are at most $1 - \log 2 - \varepsilon$ occur as a value $f_n(x)$ with $n \ge 1$ and
$x$ real; here $\log$ is the natural logarithm.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 5 (ii) (`integers-2024-A37-thm-5`). -/
public theorem_wanted floor_gaps_inter_Iic_finite {ε : ℝ} (hε : 0 < ε) :
    ({y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ, y = ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x} ∩
      Set.Iic (1 - Real.log 2 - ε)).Finite

/-- **Recursion between consecutive Farey staircases.** Let $n \ge 2$ be a natural number and $x$
a real number, write $A_m$ for the Farey staircase of order $m$, and let
$D_n(x) = A_n(x) - A_{n-1}(x)$. Then
$D_n(x) = \frac{1}{n} \left( \lfloor nx \rfloor / n - A_{n-1}(x) \right)$ and
$D_n(x) = \frac{1}{n-1} \left( \lfloor nx \rfloor / n - A_n(x) \right)$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Proposition 7 (`integers-2024-A37-prop-7`). -/
public theorem_wanted fareyStaircase_sub_eq {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    fareyStaircase n x - fareyStaircase (n - 1) x =
        (n : ℝ)⁻¹ * (⌊(n : ℝ) * x⌋ / n - fareyStaircase (n - 1) x) ∧
      fareyStaircase n x - fareyStaircase (n - 1) x =
        ((n : ℝ) - 1)⁻¹ * (⌊(n : ℝ) * x⌋ / n - fareyStaircase n x)

/-- **Bounds comparing the Farey staircase with $\lfloor nx \rfloor / n$.** For every natural
number $n \ge 1$ and every real number $x$, the Farey staircase $A_n$ of order $n$ satisfies
$A_n(x) \le \lfloor nx \rfloor / n \le A_n(x) + (\log n)/n$, where $\log$ is the natural
logarithm.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (a) (`integers-2024-A37-lem-8`). -/
public theorem_wanted fareyStaircase_le_floor_div {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    fareyStaircase n x ≤ ⌊(n : ℝ) * x⌋ / n ∧
      (⌊(n : ℝ) * x⌋ : ℝ) / n ≤ fareyStaircase n x + Real.log n / n

/-- **Bounds on the increment of the Farey staircase.** Let $n \ge 2$ be a natural number and $x$
a real number, and write $A_m$ for the Farey staircase of order $m$. Then
$0 \le A_n(x) - A_{n-1}(x) \le \frac{\log n}{n(n-1)}$, where $\log$ is the natural logarithm.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (b) (`integers-2024-A37-lem-8`). -/
public theorem_wanted fareyStaircase_sub_mem_Icc {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    0 ≤ fareyStaircase n x - fareyStaircase (n - 1) x ∧
      fareyStaircase n x - fareyStaircase (n - 1) x ≤ Real.log n / (n * (n - 1))

/-- **Harmonic blocks versus the logarithmic integral.** Let $(a_n)$ and $(b_n)$ be sequences of
natural numbers with $a_n \le b_n$ for every $n$ and $a_n \to \infty$. Then
$\sum_{k=a_n}^{b_n} 1/k - \int_{a_n}^{b_n} dt/t \to 0$ as $n \to \infty$.

In particular, if either $\sum_{k=a_n}^{b_n} 1/k$ or $\int_{a_n}^{b_n} dt/t$ converges, then so does
the other, with the same limit. Positivity of $a_n$ and $b_n$ and $b_n \to \infty$ need not be
assumed: they follow from the hypotheses (positivity for all large $n$).

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 9 (`integers-2024-A37-lem-9`). -/
public theorem_wanted tendsto_harmonic_block_sub_integral {a b : ℕ → ℕ} (hab : ∀ n, a n ≤ b n)
    (ha : Filter.Tendsto a Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => ∑ k ∈ Finset.Icc (a n) (b n), (1 / k : ℝ) - ∫ t in (a n : ℝ)..(b n), t⁻¹)
      Filter.atTop (nhds 0)

/-- **Dilation derivative of a differentiable function.** Let $f : \mathbb{R} \to \mathbb{R}$ have
derivative $f'$ at the point $x \in \mathbb{R}$. Then the quotient
$(\lambda^{-1} f(\lambda x) - f(x))/(\lambda - 1)$ tends to $x f' - f(x)$ as $\lambda \to 1$ with
$\lambda \ne 1$; that is, the dilation derivative of $f$ at $x$ exists and equals $x f' - f(x)$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Proposition 12 (`integers-2024-A37-prop-12`); dilation derivative as defined
before it. -/
public theorem_wanted tendsto_dilation_quotient {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    Filter.Tendsto (fun l : ℝ => (l⁻¹ * f (l * x) - f x) / (l - 1)) (nhdsWithin 1 {1}ᶜ)
      (nhds (x * f' - f x))

end

end MetaMathlibExt

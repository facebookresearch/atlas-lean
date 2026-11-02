/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Analysis.SpecialFunctions.Log.IntegralDerivative
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.PrimeCounting
public import WantedExt.NumberTheory.PrimeCounting.DusartMertensLogSumWanted
public import WantedExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Axler's six-term upper bound for the prime-counting function.** Let $\pi(x)$ denote the
number of primes $p \le x$ and $\log$ the natural logarithm. For every real $x \ge 48$,
$$
\pi(x) < \frac{x}{\log x - 1 - \frac{1}{\log x} - \frac{3.024334}{\log^2 x} -
\frac{12.975666}{\log^3 x} - \frac{71.048668}{\log^4 x} - \frac{461.364417856444}{\log^5 x} -
\frac{4331.1}{\log^6 x}}.
$$

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 2 (`integers-2024-A34-thm-2`). -/
public theorem_wanted primeCounting_lt_div_log_sub_six_terms (x : ℝ) (hx : 48 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / (Real.log x - 1 - 1 / Real.log x - 3.024334 / Real.log x ^ 2 -
        12.975666 / Real.log x ^ 3 - 71.048668 / Real.log x ^ 4 -
        461.364417856444 / Real.log x ^ 5 - 4331.1 / Real.log x ^ 6)

/-- **Axler's six-term lower bound for the prime-counting function.** For every real
$x \ge 1751189194177$ (the prime $p_{64497259289}$),
$$
\pi(x) > \frac{x}{\log x - 1 - \frac{1}{\log x} - \frac{2.975666}{\log^2 x} -
\frac{13.024334}{\log^3 x} - \frac{70.951332}{\log^4 x} - \frac{b_5}{\log^5 x} -
\frac{b_6}{\log^6 x}},
$$
where $b_5 = 460.634397856444$, $b_6 = 3444.031844143556$ and $\pi(x)$ is the number of primes
$p \le x$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 3 (`integers-2024-A34-thm-3`). -/
public theorem_wanted div_log_sub_six_terms_lt_primeCounting (x : ℝ)
    (hx : 1751189194177 ≤ x) :
    x / (Real.log x - 1 - 1 / Real.log x - 2.975666 / Real.log x ^ 2 -
        13.024334 / Real.log x ^ 3 - 70.951332 / Real.log x ^ 4 -
        460.634397856444 / Real.log x ^ 5 - 3444.031844143556 / Real.log x ^ 6) <
      (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- **Axler's unconditional three-term lower bound for the prime-counting function.** Let
$\pi(x)$ denote the number of primes $p \le x$ and $\log$ the natural logarithm. For every real
$x \ge 65405887$,
$$
\pi(x) > \frac{x}{\log x - 1 - \frac{1}{\log x} - \frac{3}{\log^2 x}}.
$$

This is the paper's inequality (14). Before, it was known on the interval
$[65405887, 2.7358 \cdot 10^{40}]$, for $x \ge 4.8447 \cdot 10^{19377}$, and for all
$x \ge 65405887$ under the Riemann hypothesis.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 4 (`integers-2024-A34-thm-4`), inequality (14). -/
public theorem_wanted div_log_sub_three_terms_lt_primeCounting (x : ℝ) (hx : 65405887 ≤ x) :
    x / (Real.log x - 1 - 1 / Real.log x - 3 / Real.log x ^ 2) <
      (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- **Axler's upper bound for the prime-counting function above 29.53.** Let $\pi(x)$ denote the
number of primes $p \le x$ and $\log$ the natural logarithm. For every real $x \ge 29.53$,
$$
\pi(x) < \frac{x}{\log x - 1 - \frac{1}{\log x} - \frac{3}{\log^2 x} - \frac{70.935}{\log^3 x}}.
$$

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 4 (`integers-2024-A34-prop-4`). -/
public theorem_wanted primeCounting_lt_div_log_sub_four_terms (x : ℝ) (hx : 29.53 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / (Real.log x - 1 - 1 / Real.log x - 3 / Real.log x ^ 2 - 70.935 / Real.log x ^ 3)

/-- **Eight-term upper bound for the prime-counting function.** For every real $x > 1$, the
number $\pi(x)$ of primes $p \le x$ satisfies
$\pi(x) < \frac{x}{\log x} + \frac{x}{\log^2 x} + \frac{2x}{\log^3 x} +
\frac{6.024334\,x}{\log^4 x} + \frac{24.024334\,x}{\log^5 x} + \frac{120.12167\,x}{\log^6 x} +
\frac{720.73002\,x}{\log^7 x} + \frac{6098\,x}{\log^8 x}$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 5 (`integers-2024-A34-prop-5`). -/
public theorem_wanted primeCounting_lt_eight_term_series (x : ℝ) (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
        6.024334 * x / Real.log x ^ 4 + 24.024334 * x / Real.log x ^ 5 +
        120.12167 * x / Real.log x ^ 6 + 720.73002 * x / Real.log x ^ 7 +
        6098 * x / Real.log x ^ 8

/-- **Axler's four-term series lower bound for the prime-counting function.** Let $\pi(x)$ denote
the number of primes $p \le x$ and $\log$ the natural logarithm. For every real $x \ge 10384261$,
$$
\pi(x) > \frac{x}{\log x} + \frac{x}{\log^2 x} + \frac{2x}{\log^3 x} + \frac{6x}{\log^4 x}.
$$

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 6 (`integers-2024-A34-cor-6`). -/
public theorem_wanted four_term_series_lt_primeCounting (x : ℝ) (hx : 10384261 ≤ x) :
    x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 + 6 * x / Real.log x ^ 4 <
      (Nat.primeCounting ⌊x⌋₊ : ℝ)


/-- **Axler's primes in short intervals.** Let $\log$ denote the natural logarithm, and put
$a = 1/(1.42969 \cdot 10^{12} - 1)$ and $b = 1/(1.59753 \cdot 10^{12} - 1)$. For every real
$x \ge 952527672606693$ there is a prime $p$ with $x < p \le x\,(1 + 43a/\log x)$. Moreover, for
each of the pairs $(n, X_n)$ equal to $(2, 684943746324434)$, $(3, 543684371469081)$,
$(4, 336149866771577)$ and $(5, 246782656239427)$, and every real $x \ge X_n$, there is a prime
$p$ with $x < p \le x\,(1 + 46^n b/\log^n x)$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 1 and Table 1 (`integers-2024-A34-thm-1`). -/
public theorem_wanted exists_prime_mem_Ioc_mul_one_add_div_log_pow :
    (∀ x : ℝ, 952527672606693 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧
      (p : ℝ) ≤ x * (1 + 43 / (1429690000000 - 1) / Real.log x)) ∧
    ∀ n : ℕ, ∀ X₀ : ℝ, (n, X₀) ∈ [(2, 684943746324434), (3, 543684371469081),
        (4, 336149866771577), (5, 246782656239427)] →
      ∀ x : ℝ, X₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧
        (p : ℝ) ≤ x * (1 + 46 ^ n / (1597530000000 - 1) / Real.log x ^ n)

/-- **Axler's Table 2 upper bounds for the prime-counting function.** Let $\pi(x)$ denote the
number of primes $p \le x$ and $\log$ the natural logarithm. For each of the three rows
$(a_0, a_1, a_2, x_0)$ equal to $(1.0343, 0, 0, 106640139304611)$, $(1, 1.109, 0, 81250795096339)$
and $(1, 1, 3.48, 145413088724077)$, every real $x \ge x_0$ satisfies
$$
\pi(x) < \frac{x}{\log x - a_0 - \frac{a_1}{\log x} - \frac{a_2}{\log^2 x}}.
$$

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 1 and Table 2 (`integers-2024-A34-cor-1`). -/
public theorem_wanted primeCounting_lt_div_log_sub_table_two :
    ∀ a₀ a₁ a₂ x₀ : ℝ, (a₀, a₁, a₂, x₀) ∈ [(1.0343, 0, 0, 106640139304611),
        (1, 1.109, 0, 81250795096339), (1, 1, 3.48, 145413088724077)] →
      ∀ x : ℝ, x₀ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) <
        x / (Real.log x - a₀ - a₁ / Real.log x - a₂ / Real.log x ^ 2)

/-- **Axler's Table 3 upper bounds for the prime-counting function.** Let $\pi(x)$ denote the
number of primes $p \le x$ and $\log$ the natural logarithm. For each of the three rows
$(a_3, a_4, a_5, x_0)$ equal to $(14.893, 0, 0, 142464507937911)$, $(12.975666, 79.962, 0, 22)$
and $(12.975666, 71.048668, 533.594, 32)$, every real $x \ge x_0$ satisfies
$$
\pi(x) < \frac{x}{\log x - 1 - \frac{1}{\log x} - \frac{3.024334}{\log^2 x} -
\frac{a_3}{\log^3 x} - \frac{a_4}{\log^4 x} - \frac{a_5}{\log^5 x}}.
$$

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 2 and Table 3 (`integers-2024-A34-cor-2`). -/
public theorem_wanted primeCounting_lt_div_log_sub_table_three :
    ∀ a₃ a₄ a₅ x₀ : ℝ, (a₃, a₄, a₅, x₀) ∈ [(14.893, 0, 0, 142464507937911),
        (12.975666, 79.962, 0, 22), (12.975666, 71.048668, 533.594, 32)] →
      ∀ x : ℝ, x₀ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) <
        x / (Real.log x - 1 - 1 / Real.log x - 3.024334 / Real.log x ^ 2 -
          a₃ / Real.log x ^ 3 - a₄ / Real.log x ^ 4 - a₅ / Real.log x ^ 5)

/-- **Three-term upper bounds for the prime-counting function (Table 4).** Let $\pi(x)$ be the
number of primes $p \le x$. For each of the twelve pairs $(\varepsilon, x_0)$ listed below and
every real $x \ge x_0$,
$\pi(x) < \frac{x}{\log x} + \frac{x}{\log^2 x} + \frac{(2 + \varepsilon)\,x}{\log^3 x}$.
The pairs are $(0.21, 160930932942272)$, $(0.215, 83016503500865)$,
$(0.22, 43999690220699)$, $(0.225, 23824649646672)$, $(0.23, 13279102022111)$,
$(0.24, 4511700549332)$, $(0.25, 1615202653795)$, $(0.26, 643809266445)$,
$(0.2651, 406742886708)$, $(0.27, 265248130170)$, $(0.28, 117997473286)$ and
$(0.29, 57720805589)$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 3 and Table 4 (`integers-2024-A34-cor-3`). -/
public theorem_wanted primeCounting_lt_three_term_series_table_four :
    ∀ ε x₀ : ℝ, (ε, x₀) ∈ [(0.21, 160930932942272), (0.215, 83016503500865),
        (0.22, 43999690220699), (0.225, 23824649646672), (0.23, 13279102022111),
        (0.24, 4511700549332), (0.25, 1615202653795), (0.26, 643809266445),
        (0.2651, 406742886708), (0.27, 265248130170), (0.28, 117997473286),
        (0.29, 57720805589)] →
      ∀ x : ℝ, x₀ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) <
        x / Real.log x + x / Real.log x ^ 2 + (2 + ε) * x / Real.log x ^ 3

/-- **Axler's Table 5 lower bounds for the prime-counting function.** Let $\pi(x)$ denote the
number of primes $p \le x$ and $\log$ the natural logarithm. For each of the four rows
$(a_3, a_4, a_5, x_0)$ equal to $(13.024334, 70.951332, 460.634397856444, 1035745443241)$,
$(13.024334, 70.951332, 0, 153887581621)$, $(13.024334, 0, 0, 7713187213)$ and
$(0, 0, 0, 54941209)$, every real $x \ge x_0$ satisfies
$$
\pi(x) > \frac{x}{\log x - 1 - \frac{1}{\log x} - \frac{2.975666}{\log^2 x} -
\frac{a_3}{\log^3 x} - \frac{a_4}{\log^4 x} - \frac{a_5}{\log^5 x}}.
$$

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 4 and Table 5 (`integers-2024-A34-cor-4`). -/
public theorem_wanted div_log_sub_table_five_lt_primeCounting :
    ∀ a₃ a₄ a₅ x₀ : ℝ, (a₃, a₄, a₅, x₀) ∈
        [(13.024334, 70.951332, 460.634397856444, 1035745443241),
          (13.024334, 70.951332, 0, 153887581621), (13.024334, 0, 0, 7713187213),
          (0, 0, 0, 54941209)] →
      ∀ x : ℝ, x₀ ≤ x →
        x / (Real.log x - 1 - 1 / Real.log x - 2.975666 / Real.log x ^ 2 -
          a₃ / Real.log x ^ 3 - a₄ / Real.log x ^ 4 - a₅ / Real.log x ^ 5) <
          (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- **Axler's Table 6 lower bounds for the prime-counting function.** Let $\pi(x)$ denote the
number of primes $p \le x$ and $\log$ the natural logarithm. For each of the five rows
$(b_5, b_6, b_7, b_8, x_0)$ equal to
$(23.975666, 119.87833, 719.26998, 5034.88986, 1681111802141)$,
$(23.975666, 119.87833, 719.26998, 0, 721733241667)$,
$(23.975666, 119.87833, 0, 0, 110838719141)$, $(23.975666, 0, 0, 0, 1331691853)$ and
$(0, 0, 0, 0, 10383799)$, every real $x \ge x_0$ satisfies
$$
\pi(x) > \frac{x}{\log x} + \frac{x}{\log^2 x} + \frac{2x}{\log^3 x} +
\frac{5.975666\,x}{\log^4 x} + \frac{b_5 x}{\log^5 x} + \frac{b_6 x}{\log^6 x} +
\frac{b_7 x}{\log^7 x} + \frac{b_8 x}{\log^8 x}.
$$

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 5 and Table 6 (`integers-2024-A34-cor-5`). -/
public theorem_wanted eight_term_series_table_six_lt_primeCounting :
    ∀ b₅ b₆ b₇ b₈ x₀ : ℝ, (b₅, b₆, b₇, b₈, x₀) ∈
        [(23.975666, 119.87833, 719.26998, 5034.88986, 1681111802141),
          (23.975666, 119.87833, 719.26998, 0, 721733241667),
          (23.975666, 119.87833, 0, 0, 110838719141), (23.975666, 0, 0, 0, 1331691853),
          (0, 0, 0, 0, 10383799)] →
      ∀ x : ℝ, x₀ ≤ x →
        x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
          5.975666 * x / Real.log x ^ 4 + b₅ * x / Real.log x ^ 5 + b₆ * x / Real.log x ^ 6 +
          b₇ * x / Real.log x ^ 7 + b₈ * x / Real.log x ^ 8 <
          (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- **Axler's cubic-logarithm bound for Chebyshev's theta function.** For every real
$x \ge 1757126630797$ (the prime $p_{64707865143}$),
$$
|\vartheta(x) - x| < \frac{0.024334\, x}{\log^3 x},
$$
where $\vartheta(x) = \sum_{p \le x} \log p$ is Chebyshev's function, the sum over the primes
$p \le x$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 1 (`integers-2024-A34-prop-1`), inequality (6). -/
public theorem_wanted abs_theta_sub_lt_div_log_cube (x : ℝ) (hx : 1757126630797 ≤ x) :
    |Chebyshev.theta x - x| < 0.024334 * x / Real.log x ^ 3

/-- **Axler's four bounds for Chebyshev's theta function.** Let
$\vartheta(x) = \sum_{p \le x} \log p$ be Chebyshev's function, the sum over the primes
$p \le x$. Then for real $x$ we have
$|\vartheta(x) - x| < 0.043\, x / \log^3 x$ for $x \ge e^{40}$,
$|\vartheta(x) - x| < 0.15\, x / \log^3 x$ for $e^{35} \le x < e^{5000}$,
$|\vartheta(x) - x| < 99.07\, x / \log^4 x$ for $x \ge e^{25}$, and
$|\vartheta(x) - x| < 100\, x / \log^4 x$ for $x \ge 70111$.

These bounds are re-established after the correction of Faber and Kadiri's bounds.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 3 (`integers-2024-A34-prop-3`), inequalities
(25)-(28). -/
public theorem_wanted abs_theta_sub_lt_axler_four_bounds :
    (∀ x : ℝ, Real.exp 40 ≤ x → |Chebyshev.theta x - x| < 0.043 * x / Real.log x ^ 3) ∧
    (∀ x : ℝ, Real.exp 35 ≤ x → x < Real.exp 5000 →
      |Chebyshev.theta x - x| < 0.15 * x / Real.log x ^ 3) ∧
    (∀ x : ℝ, Real.exp 25 ≤ x → |Chebyshev.theta x - x| < 99.07 * x / Real.log x ^ 4) ∧
    (∀ x : ℝ, 70111 ≤ x → |Chebyshev.theta x - x| < 100 * x / Real.log x ^ 4)

/-- **Axler's explicit Mertens second theorem.** For every real $x \ge 1757126630797$,
$$
\Big|\sum_{p \le x} \frac{1}{p} - \log\log x - B\Big| \le
\frac{0.024334}{3 \log^3 x} \Big(1 + \frac{15}{4 \log x}\Big),
$$
where the sum runs over the primes $p \le x$ and $B$ is the Meissel–Mertens constant, the limit
of $\sum_{p \le n} 1/p - \log\log n$ as the integer $n$ tends to infinity. It equals
$\gamma + \sum_p (\log(1 - 1/p) + 1/p)$, with $\gamma$ Euler's constant.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 5 (`integers-2024-A34-thm-5`), inequality (17). -/
public theorem_wanted abs_sum_inv_prime_sub_log_log_sub_le (x : ℝ) (hx : 1757126630797 ≤ x) :
    |(∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), 1 / (p : ℝ)) -
        Real.log (Real.log x) - meisselMertensConstant| ≤
      0.024334 / (3 * Real.log x ^ 3) * (1 + 15 / (4 * Real.log x))

/-- **Axler's explicit Mertens first theorem.** For every real $x \ge 1757126630797$,
$$
\Big|\sum_{p \le x} \frac{\log p}{p} - \log x - E\Big| \le
\frac{0.024334}{2 \log^2 x} \Big(1 + \frac{2}{\log x}\Big),
$$
where the sum runs over the primes $p \le x$ and $E$ is Mertens' constant, the limit of
$\sum_{p \le n} \log p / p - \log n$ as the integer $n$ tends to infinity. It equals
$-\gamma - \sum_p \log p / (p(p-1)) = -1.3325\ldots$, with $\gamma$ Euler's constant.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 6 (`integers-2024-A34-thm-6`). -/
public theorem_wanted abs_sum_log_div_prime_sub_log_sub_le (x : ℝ) (hx : 1757126630797 ≤ x) :
    |(∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), Real.log p / (p : ℝ)) -
        Real.log x - mertensConstant| ≤
      0.024334 / (2 * Real.log x ^ 2) * (1 + 2 / Real.log x)

/-- **Explicit Mertens third theorem.** Let $\gamma$ be the Euler–Mascheroni constant and
$f(x) = \frac{0.024334}{3 \log^3 x} \left(1 + \frac{15}{4 \log x}\right)$. For every real
$x \ge 1757126630797$, the product over the primes $p \le x$ satisfies
$\frac{e^{-\gamma}}{\log x} \exp(-f(x)) < \prod_{p \le x} \left(1 - \frac{1}{p}\right) <
\frac{e^{-\gamma}}{\log x} \exp\left(f(x) + \frac{1.02}{(x - 1) \log x}\right)$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 7 (`integers-2024-A34-prop-7`). -/
public theorem_wanted prod_one_sub_inv_prime_bounds (x : ℝ) (hx : 1757126630797 ≤ x) :
    Real.exp (-Real.eulerMascheroniConstant) / Real.log x *
        Real.exp (-(0.024334 / (3 * Real.log x ^ 3) * (1 + 15 / (4 * Real.log x)))) <
      ∏ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 - 1 / (p : ℝ)) ∧
    ∏ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 - 1 / (p : ℝ)) <
      Real.exp (-Real.eulerMascheroniConstant) / Real.log x *
        Real.exp (0.024334 / (3 * Real.log x ^ 3) * (1 + 15 / (4 * Real.log x)) +
          1.02 / ((x - 1) * Real.log x))

/-- **Explicit bounds for $\prod_{p \le x} (1 + 1/p)$.** Let $\gamma$ be the Euler–Mascheroni
constant and $f(x) = \frac{0.024334}{3 \log^3 x} \left(1 + \frac{15}{4 \log x}\right)$. For every
real $x \ge 1757126630797$, the product over the primes $p \le x$ satisfies
$\frac{6 e^{\gamma}}{\pi^2} \exp\left(-f(x) - \frac{1.02}{(x - 1) \log x}\right) \log x <
\prod_{p \le x} \left(1 + \frac{1}{p}\right) <
\frac{6 e^{\gamma}}{\pi^2} \left(1 + \frac{1}{x}\right) \exp(f(x)) \log x$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 7 (`integers-2024-A34-cor-7`). -/
public theorem_wanted prod_one_add_inv_prime_bounds (x : ℝ) (hx : 1757126630797 ≤ x) :
    6 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2 *
        Real.exp (-(0.024334 / (3 * Real.log x ^ 3) * (1 + 15 / (4 * Real.log x))) -
          1.02 / ((x - 1) * Real.log x)) * Real.log x <
      ∏ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 + 1 / (p : ℝ)) ∧
    ∏ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), (1 + 1 / (p : ℝ)) <
      6 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2 * (1 + 1 / x) *
        Real.exp (0.024334 / (3 * Real.log x ^ 3) * (1 + 15 / (4 * Real.log x))) *
        Real.log x


/-- **Converting a lower bound for $\pi(x)$ into a truncated series.** Let $\pi(x)$ be the number
of primes $p \le x$. Let $n \ge 1$ be an integer, let $a_0, \dots, a_n$ be reals with $a_0 > 0$
and $a_1, \dots, a_n < 0$, and let $x_0 > 0$. Suppose that for every real $x \ge x_0$ the
denominator $D(x) = a_0 \log x + \sum_{i=1}^{n} a_i / \log^{i-1} x$ is positive and
$\pi(x) > x / D(x)$. Let $b_0 = 1/a_0$ and $b_k = -\frac{1}{a_0} \sum_{i=1}^{k} a_i b_{k-i}$ for
$1 \le k \le n$. Then for every real $x \ge x_0$,
$\pi(x) > \sum_{k=0}^{n} \frac{b_k x}{\log^{k+1} x}$.

The recursion uses $b_{k-i}$, the index of the paper's proof: it turns the first row of Table 5
into the Table 6 coefficients $1, 1, 2, 5.975666, 23.975666, \dots$. The source record of the
statement prints $b_{k-1}$ instead, which would give $b_3 = 9.951332$ there.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 6 (`integers-2024-A34-prop-6`). -/
public theorem_wanted series_lt_primeCounting_of_lt_primeCounting (n : ℕ) (hn : 1 ≤ n)
    (a b : ℕ → ℝ) (ha₀ : 0 < a 0) (ha : ∀ i ∈ Finset.Icc 1 n, a i < 0) (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hpos : ∀ x : ℝ, x₀ ≤ x →
      0 < a 0 * Real.log x + ∑ i ∈ Finset.Icc 1 n, a i / Real.log x ^ (i - 1))
    (hlow : ∀ x : ℝ, x₀ ≤ x →
      x / (a 0 * Real.log x + ∑ i ∈ Finset.Icc 1 n, a i / Real.log x ^ (i - 1)) <
        (Nat.primeCounting ⌊x⌋₊ : ℝ))
    (hb₀ : b 0 = 1 / a 0)
    (hb : ∀ k ∈ Finset.Icc 1 n, b k = -(1 / a 0) * ∑ i ∈ Finset.Icc 1 k, a i * b (k - i))
    (x : ℝ) (hx : x₀ ≤ x) :
    ∑ k ∈ Finset.range (n + 1), b k * x / Real.log x ^ (k + 1) <
      (Nat.primeCounting ⌊x⌋₊ : ℝ)


/-- **Prime counting between the auxiliary functions $J$.** Let $\pi(x)$ be the number of primes
$p \le x$ and $\vartheta(x) = \sum_{p \le x} \log p$ Chebyshev's function. Let $k \ge 1$ be an
integer and let $\eta > 0$ and $x_1 > 1$ be reals with $|\vartheta(y) - y| < \eta y / \log^k y$
for every real $y \ge x_1$. For reals $e$ and $x \ge x_1$ set
$J_e(x) = \pi(x_1) - \frac{\vartheta(x_1)}{\log x_1} + \frac{x}{\log x} +
\frac{e\,x}{\log^{k+1} x} + \int_{x_1}^{x} \left(\frac{1}{\log^2 t} +
\frac{e}{\log^{k+2} t}\right) dt$.
Then $J_{-\eta}(x) \le \pi(x) \le J_{\eta}(x)$ for every real $x \ge x_1$.

The inequalities are non-strict, as the paper prints them.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 1 (`integers-2024-A34-lem-1`). -/
public theorem_wanted primeCounting_mem_Icc_auxJ (k : ℕ) (hk : 0 < k) (η x₁ : ℝ) (hη : 0 < η)
    (hx₁ : 1 < x₁)
    (hθ : ∀ y : ℝ, x₁ ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y ^ k)
    (x : ℝ) (hx : x₁ ≤ x) :
    let J : ℝ → ℝ := fun e =>
      (Nat.primeCounting ⌊x₁⌋₊ : ℝ) - Chebyshev.theta x₁ / Real.log x₁ + x / Real.log x +
        e * x / Real.log x ^ (k + 1) +
          ∫ t in x₁..x, (1 / Real.log t ^ 2 + e / Real.log t ^ (k + 2))
    J (-η) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ J η

/-- **Büthe's bound of the prime-counting function by the logarithmic integral.** Let $\pi(x)$
denote the number of primes $p \le x$, and let $\operatorname{li}(x)$ be the logarithmic integral,
the principal value $\mathrm{PV}\int_0^x \frac{dt}{\log t}$. For every real $x$ with
$2 \le x \le 10^{19}$, $\pi(x) \le \operatorname{li}(x)$.

The paper prints the non-strict form; Büthe's original bound is strict.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 2 (Büthe) (`integers-2024-A34-lem-2`). -/
public theorem_wanted primeCounting_le_logarithmicIntegral (x : ℝ) (hx : 2 ≤ x)
    (hx' : x ≤ 10 ^ 19) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Real.logarithmicIntegralReal x

/-- **Johnston's range for Schoenfeld's inequality.** For every real $x$ with
$2657 \le x \le 1.101 \cdot 10^{26}$,
$$
|\pi(x) - \operatorname{li}(x)| < \frac{\sqrt{x} \log x}{8\pi},
$$
where $\pi(x)$ is the number of primes $p \le x$ and $\operatorname{li}$ is the logarithmic
integral.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 3 (Johnston) (`integers-2024-A34-lem-3`). -/
public theorem_wanted abs_primeCounting_sub_logarithmicIntegral_lt (x : ℝ) (hx : 2657 ≤ x)
    (hx' : x ≤ 1.101 * 10 ^ 26) :
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logarithmicIntegralReal x| <
      Real.sqrt x * Real.log x / (8 * Real.pi)

/-- **Tails of prime power sums from a Chebyshev bound.** Let $k \ge 1$ be an integer and let
$\eta > 0$ and $x_0 > 1$ be reals such that $|\vartheta(y) - y| < \eta y / \log^k y$ for every
real $y \ge x_0$, where $\vartheta(y) = \sum_{p \le y} \log p$ is Chebyshev's function. Then
for every integer $n \ge 2$ and every real $x \ge x_0$,
$$
\Big|\operatorname{li}(x^{1-n}) + \sum_{p > x} \frac{1}{p^n}\Big| <
\frac{\eta}{x^{n-1} \log^{k+1} x} \Big(1 + \frac{n}{n-1}\Big),
$$
where $\operatorname{li}$ is the logarithmic integral and the sums run over primes $p$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 6 (`integers-2024-A34-lem-6`). -/
public theorem_wanted abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt (k : ℕ) (hk : 0 < k)
    (η x₀ : ℝ) (hη : 0 < η) (hx₀ : 1 < x₀)
    (hθ : ∀ y : ℝ, x₀ ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y ^ k)
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : x₀ ≤ x) :
    |Real.logarithmicIntegralReal (x ^ ((1 : ℝ) - n)) +
        ∑' p : ℕ, if p.Prime ∧ x < p then 1 / (p : ℝ) ^ n else 0| <
      η / (x ^ (n - 1) * Real.log x ^ (k + 1)) * (1 + n / (n - 1 : ℝ))

/-- **The Mertens remainder from a Chebyshev bound.** Let $k \ge 1$ be an integer and let
$\eta > 0$ and $x_0 > 1$ be reals such that $|\vartheta(y) - y| < \eta y / \log^k y$ for every
real $y \ge x_0$, where $\vartheta(y) = \sum_{p \le y} \log p$ is Chebyshev's function. For
real $x$ let $S(x) = \sum_{p > x} \big(\log(1 - 1/p) + 1/p\big)$, the sum over the primes
$p > x$. Then for every real $x \ge x_0$,
$$
\Big|S(x) - \sum_{m \ge 1} \frac{\operatorname{li}(x^{-m})}{m+1}\Big| <
\frac{\eta}{\log^{k+1} x} \Big((x+1) \log\frac{x}{x-1} - 1\Big),
$$
where $\operatorname{li}$ is the logarithmic integral.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 8 (`integers-2024-A34-prop-8`); `S(x)` as in
the paper's equation (6.5). -/
public theorem_wanted abs_mertensRemainder_sub_tsum_logarithmicIntegral_lt (k : ℕ) (hk : 0 < k)
    (η x₀ : ℝ) (hη : 0 < η) (hx₀ : 1 < x₀)
    (hθ : ∀ y : ℝ, x₀ ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y ^ k)
    (x : ℝ) (hx : x₀ ≤ x) :
    |(∑' p : ℕ, if p.Prime ∧ x < p then Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) else 0) -
        ∑' m : ℕ, Real.logarithmicIntegralReal (x ^ (-((m : ℝ) + 1))) / ((m : ℝ) + 2)| <
      η / Real.log x ^ (k + 1) * ((x + 1) * Real.log (x / (x - 1)) - 1)

/-- **Tails of prime power sums under the Riemann hypothesis.** Assume the Riemann
hypothesis. Then for every integer $n \ge 2$ and every real $x \ge 599$,
$$
\Big|\operatorname{li}(x^{1-n}) + \sum_{p > x} \frac{1}{p^n}\Big| <
\frac{1}{8\pi x^{n - 1/2}} \Big(1 + \frac{2n}{2n-1}\Big) \Big(\log x + \frac{2}{2n-1}\Big),
$$
where $\operatorname{li}$ is the logarithmic integral and the sum runs over the primes $p > x$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 9 (`integers-2024-A34-prop-9`). -/
public theorem_wanted abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt_of_RH
    (hRH : RiemannHypothesis) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 599 ≤ x) :
    |Real.logarithmicIntegralReal (x ^ ((1 : ℝ) - n)) +
        ∑' p : ℕ, if p.Prime ∧ x < p then 1 / (p : ℝ) ^ n else 0| <
      1 / (8 * Real.pi * x ^ ((n : ℝ) - 1 / 2)) * (1 + 2 * n / (2 * n - 1 : ℝ)) *
        (Real.log x + 2 / (2 * n - 1 : ℝ))

/-- **The last branch of Axler's error factor is nonincreasing.** Let $R = 5.5666305$ and for
real $y \ge e^{673}$ let
$$
a(y) = \log^6 y \cdot 121.0961 \Big(\frac{\log y}{R}\Big)^{3/2}
\exp\Big(-2\sqrt{\frac{\log y}{R}}\Big).
$$
Then $a(x) \le a(x_1)$ for all reals $x_1$ and $x$ with $e^{673} \le x_1 \le x$.

This is the paper's function $a$ on $y \ge e^{673}$. The paper prints the statement as
$a_n(x) \le a_n(x_1)$; its proof ($a'(x) < 0$ for $x \ge e^{673}$) and the later use
$a(t) \le a(x_1)$ show that $a_n$ is a typo for $a$.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 5 (`integers-2024-A34-lem-5`), with the function `a`
defined at the start of Section 6. -/
public theorem_wanted axlerThetaErrorFactor_tail_antitone (x₁ x : ℝ)
    (hx₁ : Real.exp 673 ≤ x₁) (hx : x₁ ≤ x) :
    Real.log x ^ 6 * (121.0961 * (Real.log x / 5.5666305) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (Real.log x / 5.5666305))) ≤
      Real.log x₁ ^ 6 * (121.0961 * (Real.log x₁ / 5.5666305) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (Real.log x₁ / 5.5666305)))

end

end MetaMathlibExt

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

/-- Upper bound for the prime-counting function matching the first terms of its asymptotic
expansion: for every real `x ≥ 48`,
`π(x) < x / (log x - 1 - 1/log x - 3.024334/log² x - 12.975666/log³ x - 71.048668/log⁴ x -
a₅/log⁵ x - a₆/log⁶ x)` with `a₅ = 461.364417856444` and `a₆ = 4331.1`.
`π(x)` is `Nat.primeCounting ⌊x⌋₊`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 2 (`integers-2024-A34-thm-2`). -/
public theorem_wanted primeCounting_lt_div_log_sub_six_terms (x : ℝ) (hx : 48 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / (Real.log x - 1 - 1 / Real.log x - 3.024334 / Real.log x ^ 2 -
        12.975666 / Real.log x ^ 3 - 71.048668 / Real.log x ^ 4 -
        461.364417856444 / Real.log x ^ 5 - 4331.1 / Real.log x ^ 6)

/-- Lower bound for the prime-counting function matching the first terms of its asymptotic
expansion: for every real `x ≥ 1751189194177` (the prime `p₆₄₄₉₇₂₅₉₂₈₉`),
`π(x) > x / (log x - 1 - 1/log x - 2.975666/log² x - 13.024334/log³ x - 70.951332/log⁴ x -
b₅/log⁵ x - b₆/log⁶ x)` with `b₅ = 460.634397856444` and `b₆ = 3444.031844143556`.
`π(x)` is `Nat.primeCounting ⌊x⌋₊`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 3 (`integers-2024-A34-thm-3`). -/
public theorem_wanted div_log_sub_six_terms_lt_primeCounting (x : ℝ)
    (hx : 1751189194177 ≤ x) :
    x / (Real.log x - 1 - 1 / Real.log x - 2.975666 / Real.log x ^ 2 -
        13.024334 / Real.log x ^ 3 - 70.951332 / Real.log x ^ 4 -
        460.634397856444 / Real.log x ^ 5 - 3444.031844143556 / Real.log x ^ 6) <
      (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- Unconditional form of the lower bound `π(x) > x / (log x - 1 - 1/log x - 3/log² x)`
(the paper's inequality (14)), for every real `x ≥ 65405887`; earlier it was known on
`[65405887, 2.7358·10⁴⁰]`, for `x ≥ 4.8447·10¹⁹³⁷⁷`, and for all `x ≥ 65405887` under the Riemann
hypothesis. `π(x)` is `Nat.primeCounting ⌊x⌋₊`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 4 (`integers-2024-A34-thm-4`), inequality (14). -/
public theorem_wanted div_log_sub_three_terms_lt_primeCounting (x : ℝ) (hx : 65405887 ≤ x) :
    x / (Real.log x - 1 - 1 / Real.log x - 3 / Real.log x ^ 2) <
      (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- For every real `x ≥ 29.53`,
`π(x) < x / (log x - 1 - 1/log x - 3/log² x - 70.935/log³ x)`.
`π(x)` is `Nat.primeCounting ⌊x⌋₊`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 4 (`integers-2024-A34-prop-4`). -/
public theorem_wanted primeCounting_lt_div_log_sub_four_terms (x : ℝ) (hx : 29.53 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / (Real.log x - 1 - 1 / Real.log x - 3 / Real.log x ^ 2 - 70.935 / Real.log x ^ 3)

/-- For every real `x > 1`, `π(x)` is below the truncated asymptotic series
`x/log x + x/log² x + 2x/log³ x + 6.024334x/log⁴ x + 24.024334x/log⁵ x +
120.12167x/log⁶ x + 720.73002x/log⁷ x + 6098x/log⁸ x`.
`π(x)` is `Nat.primeCounting ⌊x⌋₊`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 5 (`integers-2024-A34-prop-5`). -/
public theorem_wanted primeCounting_lt_eight_term_series (x : ℝ) (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
        6.024334 * x / Real.log x ^ 4 + 24.024334 * x / Real.log x ^ 5 +
        120.12167 * x / Real.log x ^ 6 + 720.73002 * x / Real.log x ^ 7 +
        6098 * x / Real.log x ^ 8

/-- For every real `x ≥ 10384261`,
`π(x) > x/log x + x/log² x + 2x/log³ x + 6x/log⁴ x`.
`π(x)` is `Nat.primeCounting ⌊x⌋₊`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 6 (`integers-2024-A34-cor-6`). -/
public theorem_wanted four_term_series_lt_primeCounting (x : ℝ) (hx : 10384261 ≤ x) :
    x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 + 6 * x / Real.log x ^ 4 <
      (Nat.primeCounting ⌊x⌋₊ : ℝ)


/-- Primes in short intervals: with `a = (1.42969·10¹² - 1)⁻¹` and `b = (1.59753·10¹² - 1)⁻¹`,
for `1 ≤ n ≤ 5` and every real `x ≥ Xₙ` there is a prime `p` with `x < p ≤ x (1 + aₙ/logⁿ x)`,
where (Table 1) `a₁ = 43a`, `X₁ = 952527672606693` and `aₙ = 46ⁿ b` for `n = 2, …, 5` with
`X₂ = 684943746324434`, `X₃ = 543684371469081`, `X₄ = 336149866771577`,
`X₅ = 246782656239427`. Stated as a conjunction over the five rows.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 1 and Table 1 (`integers-2024-A34-thm-1`). -/
public theorem_wanted exists_prime_mem_Ioc_mul_one_add_div_log_pow :
    (∀ x : ℝ, 952527672606693 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧
      (p : ℝ) ≤ x * (1 + 43 / (1429690000000 - 1) / Real.log x)) ∧
    ∀ n : ℕ, ∀ X₀ : ℝ, (n, X₀) ∈ [(2, 684943746324434), (3, 543684371469081),
        (4, 336149866771577), (5, 246782656239427)] →
      ∀ x : ℝ, X₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧
        (p : ℝ) ≤ x * (1 + 46 ^ n / (1597530000000 - 1) / Real.log x ^ n)

/-- Compact upper bounds `π(x) < x / (log x - a₀ - a₁/log x - a₂/log² x)` for every real
`x ≥ x₀`, for the three rows `(a₀, a₁, a₂, x₀)` of Table 2:
`(1.0343, 0, 0, 106640139304611)`, `(1, 1.109, 0, 81250795096339)`,
`(1, 1, 3.48, 145413088724077)`. `π(x)` is `Nat.primeCounting ⌊x⌋₊`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 1 and Table 2 (`integers-2024-A34-cor-1`). -/
public theorem_wanted primeCounting_lt_div_log_sub_table_two :
    ∀ a₀ a₁ a₂ x₀ : ℝ, (a₀, a₁, a₂, x₀) ∈ [(1.0343, 0, 0, 106640139304611),
        (1, 1.109, 0, 81250795096339), (1, 1, 3.48, 145413088724077)] →
      ∀ x : ℝ, x₀ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) <
        x / (Real.log x - a₀ - a₁ / Real.log x - a₂ / Real.log x ^ 2)

/-- Upper bounds `π(x) < x / (log x - 1 - 1/log x - 3.024334/log² x - a₃/log³ x - a₄/log⁴ x -
a₅/log⁵ x)` for every real `x ≥ x₀`, for the three rows `(a₃, a₄, a₅, x₀)` of Table 3:
`(14.893, 0, 0, 142464507937911)`, `(12.975666, 79.962, 0, 22)`,
`(12.975666, 71.048668, 533.594, 32)`. `π(x)` is `Nat.primeCounting ⌊x⌋₊`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Corollary 2 and Table 3 (`integers-2024-A34-cor-2`). -/
public theorem_wanted primeCounting_lt_div_log_sub_table_three :
    ∀ a₃ a₄ a₅ x₀ : ℝ, (a₃, a₄, a₅, x₀) ∈ [(14.893, 0, 0, 142464507937911),
        (12.975666, 79.962, 0, 22), (12.975666, 71.048668, 533.594, 32)] →
      ∀ x : ℝ, x₀ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) <
        x / (Real.log x - 1 - 1 / Real.log x - 3.024334 / Real.log x ^ 2 -
          a₃ / Real.log x ^ 3 - a₄ / Real.log x ^ 4 - a₅ / Real.log x ^ 5)

/-- Upper bounds `π(x) < x/log x + x/log² x + (2 + ε)x/log³ x` for every real `x ≥ x₀`, for the
twelve rows `(ε, x₀)` of Table 4. `π(x)` is `Nat.primeCounting ⌊x⌋₊`.

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

/-- Lower bounds `π(x) > x / (log x - 1 - 1/log x - 2.975666/log² x - a₃/log³ x - a₄/log⁴ x -
a₅/log⁵ x)` for every real `x ≥ x₀`, for the four rows `(a₃, a₄, a₅, x₀)` of Table 5:
`(13.024334, 70.951332, 460.634397856444, 1035745443241)`,
`(13.024334, 70.951332, 0, 153887581621)`, `(13.024334, 0, 0, 7713187213)`,
`(0, 0, 0, 54941209)`. `π(x)` is `Nat.primeCounting ⌊x⌋₊`.

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

/-- Lower bounds `π(x) > x/log x + x/log² x + 2x/log³ x + 5.975666x/log⁴ x + b₅x/log⁵ x +
b₆x/log⁶ x + b₇x/log⁷ x + b₈x/log⁸ x` for every real `x ≥ x₀`, for the five rows
`(b₅, b₆, b₇, b₈, x₀)` of Table 6. `π(x)` is `Nat.primeCounting ⌊x⌋₊`.

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

/-- The paper's inequality (6) for Chebyshev's function:
`|ϑ(x) - x| < 0.024334 x / log³ x` for every real `x ≥ 1757126630797` (the prime
`p₆₄₇₀₇₈₆₅₁₄₃`). `ϑ` is Mathlib's `Chebyshev.theta`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 1 (`integers-2024-A34-prop-1`), inequality (6). -/
public theorem_wanted abs_theta_sub_lt_div_log_cube (x : ℝ) (hx : 1757126630797 ≤ x) :
    |Chebyshev.theta x - x| < 0.024334 * x / Real.log x ^ 3

/-- The paper's inequalities (25)-(28) for Chebyshev's function, re-established after the
correction of Faber and Kadiri's bounds: `|ϑ(x) - x| < 0.043 x / log³ x` for `x ≥ e⁴⁰`,
`|ϑ(x) - x| < 0.15 x / log³ x` for `e³⁵ ≤ x < e⁵⁰⁰⁰`, `|ϑ(x) - x| < 99.07 x / log⁴ x` for
`x ≥ e²⁵`, and `|ϑ(x) - x| < 100 x / log⁴ x` for `x ≥ 70111`. `ϑ` is Mathlib's
`Chebyshev.theta`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 3 (`integers-2024-A34-prop-3`), inequalities
(25)-(28). -/
public theorem_wanted abs_theta_sub_lt_axler_four_bounds :
    (∀ x : ℝ, Real.exp 40 ≤ x → |Chebyshev.theta x - x| < 0.043 * x / Real.log x ^ 3) ∧
    (∀ x : ℝ, Real.exp 35 ≤ x → x < Real.exp 5000 →
      |Chebyshev.theta x - x| < 0.15 * x / Real.log x ^ 3) ∧
    (∀ x : ℝ, Real.exp 25 ≤ x → |Chebyshev.theta x - x| < 99.07 * x / Real.log x ^ 4) ∧
    (∀ x : ℝ, 70111 ≤ x → |Chebyshev.theta x - x| < 100 * x / Real.log x ^ 4)

/-- Explicit Mertens second theorem: for every real `x ≥ 1757126630797`,
`|∑_{p ≤ x} 1/p - log log x - B| ≤ 0.024334/(3 log³ x) · (1 + 15/(4 log x))`, where `B` is
the Meissel-Mertens constant (`meisselMertensConstant`, the limit of
`∑_{p ≤ n} 1/p - log log n`, equal to the paper's `γ + ∑_p (log(1 - 1/p) + 1/p)`).

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 5 (`integers-2024-A34-thm-5`), inequality (17). -/
public theorem_wanted abs_sum_inv_prime_sub_log_log_sub_le (x : ℝ) (hx : 1757126630797 ≤ x) :
    |(∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), 1 / (p : ℝ)) -
        Real.log (Real.log x) - meisselMertensConstant| ≤
      0.024334 / (3 * Real.log x ^ 3) * (1 + 15 / (4 * Real.log x))

/-- Explicit Mertens first theorem: for every real `x ≥ 1757126630797`,
`|∑_{p ≤ x} log p / p - log x - E| ≤ 0.024334/(2 log² x) · (1 + 2/log x)`, where `E` is
`mertensConstant` (the limit of `∑_{p ≤ n} log p / p - log n`, equal to the paper's
`E = -γ - ∑_p log p / (p (p - 1)) = -1.3325…`).

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Theorem 6 (`integers-2024-A34-thm-6`). -/
public theorem_wanted abs_sum_log_div_prime_sub_log_sub_le (x : ℝ) (hx : 1757126630797 ≤ x) :
    |(∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)), Real.log p / (p : ℝ)) -
        Real.log x - mertensConstant| ≤
      0.024334 / (2 * Real.log x ^ 2) * (1 + 2 / Real.log x)

/-- Explicit Mertens third theorem: for every real `x ≥ 1757126630797`,
`e^{-γ}/log x · exp(-f(x)) < ∏_{p ≤ x} (1 - 1/p) < e^{-γ}/log x · exp(f(x) + 1.02/((x - 1) log x))`
with `f(x) = 0.024334/(3 log³ x) · (1 + 15/(4 log x))` the right-hand side of (17).

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

/-- For every real `x ≥ 1757126630797`,
`6e^γ/π² · exp(-f(x) - 1.02/((x - 1) log x)) · log x < ∏_{p ≤ x} (1 + 1/p) <
6e^γ/π² · (1 + 1/x) · exp(f(x)) · log x`
with `f(x) = 0.024334/(3 log³ x) · (1 + 15/(4 log x))` the right-hand side of (17).

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


/-- Converting a lower bound `π(x) > x / (a₀ log x + a₁ + a₂/log x + ⋯ + aₙ/logⁿ⁻¹ x)` into a
truncated series: let `n ≥ 1`, `a₀ > 0` and `a₁, …, aₙ < 0`; if for every `x ≥ x₀ > 0` the
denominator is positive (the paper's (49)) and the lower bound (50) holds, then
`π(x) > b₀x/log x + b₁x/log² x + ⋯ + bₙx/logⁿ⁺¹ x` for every `x ≥ x₀`, where `b₀ = 1/a₀` and
`bₖ = -(1/a₀) ∑_{i=1}^k aᵢ b_{k-i}` for `1 ≤ k ≤ n`. The recursion (51) is read with
`b_{k-i}` (the index the paper's proof uses, and the one that turns Table 5, first row, into the
Table 6 coefficients `1, 1, 2, 5.975666, 23.975666, …`); the record prints `b_{k-1}`, which gives
`b₃ = 9.951332` there. `π(x)` is `Nat.primeCounting ⌊x⌋₊`.

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


/-- Prime counting between the auxiliary functions `J`: let `k ≥ 1`, `η > 0`, `x₁ > 1` with
`|ϑ(y) - y| < η y / logᵏ y` for every `y ≥ x₁`, and for real `e` set
`J_{k,e,x₁}(x) = π(x₁) - ϑ(x₁)/log x₁ + x/log x + e x/log^{k+1} x +
∫_{x₁}^{x} (1/log² t + e/log^{k+2} t) dt` (the paper's (4.1)). Then
`J_{k,-η,x₁}(x) ≤ π(x) ≤ J_{k,η,x₁}(x)` for every `x ≥ x₁` (non-strict, as the paper prints it).

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

/-- Büthe's bound: `π(x) ≤ li(x)` for every real `x` with `2 ≤ x ≤ 10¹⁹`, with `li` the
principal-value logarithmic integral `∫₀ˣ dt/log t` (`Real.logarithmicIntegralReal`, the paper's
definition) and `π(x) = Nat.primeCounting ⌊x⌋₊`. The paper prints the non-strict form; Büthe's
original bound is strict.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 2 (Büthe) (`integers-2024-A34-lem-2`). -/
public theorem_wanted primeCounting_le_logarithmicIntegral (x : ℝ) (hx : 2 ≤ x)
    (hx' : x ≤ 10 ^ 19) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Real.logarithmicIntegralReal x

/-- Johnston's unconditional range for Schoenfeld's inequality:
`|π(x) - li(x)| < √x log x / (8π)` for every real `x` with `2657 ≤ x ≤ 1.101 · 10²⁶`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 3 (Johnston) (`integers-2024-A34-lem-3`). -/
public theorem_wanted abs_primeCounting_sub_logarithmicIntegral_lt (x : ℝ) (hx : 2657 ≤ x)
    (hx' : x ≤ 1.101 * 10 ^ 26) :
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logarithmicIntegralReal x| <
      Real.sqrt x * Real.log x / (8 * Real.pi)

/-- Tails of prime power sums from a Chebyshev bound: let `k ≥ 1`, `η > 0`, `x₀ > 1` with
`|ϑ(y) - y| < η y / logᵏ y` for every `y ≥ x₀`. Then for every integer `n ≥ 2` and `x ≥ x₀`,
`|li(x^{1-n}) + ∑_{p > x} 1/pⁿ| < η (1 + n/(n-1)) / (x^{n-1} log^{k+1} x)`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Lemma 6 (`integers-2024-A34-lem-6`). -/
public theorem_wanted abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt (k : ℕ) (hk : 0 < k)
    (η x₀ : ℝ) (hη : 0 < η) (hx₀ : 1 < x₀)
    (hθ : ∀ y : ℝ, x₀ ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y ^ k)
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : x₀ ≤ x) :
    |Real.logarithmicIntegralReal (x ^ ((1 : ℝ) - n)) +
        ∑' p : ℕ, if p.Prime ∧ x < p then 1 / (p : ℝ) ^ n else 0| <
      η / (x ^ (n - 1) * Real.log x ^ (k + 1)) * (1 + n / (n - 1 : ℝ))

/-- The Mertens remainder `S(x) = ∑_{p > x} (log(1 - 1/p) + 1/p)` from a Chebyshev bound: under
the hypotheses of `abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt`, for every `x ≥ x₀`,
`|S(x) - ∑_{n ≥ 1} li(x^{-n})/(n+1)| < η ((x+1) log(x/(x-1)) - 1) / log^{k+1} x`.

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

/-- Under the Riemann hypothesis, for every integer `n ≥ 2` and real `x ≥ 599`,
`|li(x^{1-n}) + ∑_{p > x} 1/pⁿ| < (1 + 2n/(2n-1)) (log x + 2/(2n-1)) / (8π x^{n-1/2})`.

Source: Christian Axler, *Effective Estimates for Some Functions Defined over Primes*,
INTEGERS 24 (2024), Article A34, Proposition 9 (`integers-2024-A34-prop-9`). -/
public theorem_wanted abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt_of_RH
    (hRH : RiemannHypothesis) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 599 ≤ x) :
    |Real.logarithmicIntegralReal (x ^ ((1 : ℝ) - n)) +
        ∑' p : ℕ, if p.Prime ∧ x < p then 1 / (p : ℝ) ^ n else 0| <
      1 / (8 * Real.pi * x ^ ((n : ℝ) - 1 / 2)) * (1 + 2 * n / (2 * n - 1 : ℝ)) *
        (Real.log x + 2 / (2 * n - 1 : ℝ))

/-- The last branch of the paper's function `a` from Section 6 is nonincreasing: with
`R = 5.5666305` and `a(y) = log⁶ y · 121.0961 (log y / R)^{3/2} exp(-2 √(log y / R))` (the
definition of `a` for `y ≥ e⁶⁷³`), `a(x) ≤ a(x₁)` whenever `e⁶⁷³ ≤ x₁ ≤ x`. The printed
statement writes `aₙ(x) ≤ aₙ(x₁)`; the proof (`a'(x) < 0` for `x ≥ e⁶⁷³`) and the later use
`a(t) ≤ a(x₁)` show that `aₙ` is a typo for `a`.

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

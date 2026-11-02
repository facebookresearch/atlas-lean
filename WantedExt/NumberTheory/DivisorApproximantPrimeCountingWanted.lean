/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Smooth approximants of divisor functions and `π(n)` (statements)

Statement-only targets from Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula
for π(n) with the Divisor Counting Function*. The paper approximates the divisibility indicator
`[k | n]` by `exp(-n k A(k, n) sin²(nπ/k))`, where `A(k, n) sin²(nπ/k) ≥ 1` whenever `k ∤ n`.
The extraction drops the accent that distinguishes each approximant from the exact function;
the approximant is always the quantity being defined. `τ(n) = n.divisors.card`,
`σ(n) = ∑_{d ∣ n} d`, `π(n) = Nat.primeCounting n`. The paper's `A : ℕ × ℕ → ℝ⁺` is a
function `ℕ → ℕ → ℝ`; its positivity is not needed and not assumed.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset

@[expose] public section

/-- **Exponential approximation of the divisibility indicator.** Let $A$ be a real-valued
function of two natural numbers such that $A(k, n) \sin^2(n\pi/k) \ge 1$ for all natural numbers
$k, n$ with $1 \le k \le n$ and $k \nmid n$. Then for all natural numbers $k, n$ with
$1 \le k \le n$,
$$\left| e^{-nkA(k, n)\sin^2(n\pi/k)} - \delta_{k \mid n} \right| \le e^{-nk},$$
where $\delta_{k \mid n}$ is $1$ if $k$ divides $n$ and $0$ otherwise.

When $k \mid n$ the difference is $0$; otherwise it lies in $(0, e^{-nk}]$.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 1 (`integers-2026-A46-lem-1`). -/
public theorem_wanted abs_exp_approx_sub_dvd_indicator_le (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2)
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    |Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) - (if k ∣ n then 1 else 0)| ≤
      Real.exp (-(n * k : ℝ))

/-- **Exponential approximation of the divisor-counting function.** Let $A$ be a real-valued
function of two natural numbers such that $A(k, n) \sin^2(n\pi/k) \ge 1$ for all natural numbers
$k, n$ with $1 \le k \le n$ and $k \nmid n$. For a natural number $n$ let $\tau(n)$ be the number
of positive divisors of $n$ and
$$\tilde\tau(n) = \sum_{k=1}^{n} e^{-nkA(k, n)\sin^2(n\pi/k)}.$$
Then $\tilde\tau(n) - \tau(n) = O\left(\frac{1}{e^n - 1}\right)$ as $n \to \infty$.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 2 (`integers-2026-A46-lem-2`). -/
public theorem_wanted divisorCountApprox_sub_isBigO (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) -
        (n.divisors.card : ℝ)) =O[atTop] fun n : ℕ => 1 / (Real.exp n - 1)

/-- **Prime counting from the exact divisor count.** For every natural number $n \ge 2$,
$$\sum_{m=2}^{n} e^{-m(\tau(m) - 2)} - \pi(n) < \frac{1}{e^3(e - 1)},$$
where $\tau(m)$ is the number of positive divisors of $m$ and $\pi(n)$ is the number of primes at
most $n$.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 3 (`integers-2026-A46-lem-3`). -/
public theorem_wanted primeCountingApprox_sub_lt (n : ℕ) (hn : 2 ≤ n) :
    ∑ m ∈ Icc 2 n, Real.exp (-(m * ((m.divisors.card : ℝ) - 2))) - Nat.primeCounting n <
      1 / (Real.exp 3 * (Real.exp 1 - 1))

/-- **Sine lower bound at non-divisors.** For all positive integers $k$ and $n$ with $k \nmid n$,
$$\frac{\pi^2 k^2}{2} \sin^2\frac{n\pi}{k} \ge 1.$$
In other words, $A(k, n) = \pi^2 k^2 / 2$ satisfies the hypothesis
$A(k, n) \sin^2(n\pi/k) \ge 1$ of the exponential approximation of the divisibility indicator.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 4 (`integers-2026-A46-lem-4`). -/
public theorem_wanted one_le_pi_sq_mul_sq_div_two_mul_sin_sq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) (hkn : ¬ k ∣ n) :
    1 ≤ Real.pi ^ 2 * k ^ 2 / 2 * Real.sin (n * Real.pi / k) ^ 2

/-- **Trigonometric approximation of the divisor-counting function.** For a natural number $k$
let $\tau(k)$ be the number of positive divisors of $k$ and
$$\tilde\tau(k) = \sum_{j=1}^{k} \exp\left(-\frac{\pi^2}{2} k j^3 \sin^2\frac{k\pi}{j}\right).$$
Then $\tilde\tau(k) - \tau(k) = O\left(\frac{1}{e^k - 1}\right)$ as $k \to \infty$.

This is the exponential approximation of the divisor-counting function with
$A(j, k) = \pi^2 j^2 / 2$.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Theorem 1 (`integers-2026-A46-thm-1`). -/
public theorem_wanted divisorCountApprox_one_sub_isBigO :
    (fun k : ℕ => ∑ j ∈ Icc 1 k,
        Real.exp (-(Real.pi ^ 2 / 2 * k * j ^ 3 * Real.sin (k * Real.pi / j) ^ 2)) -
        (k.divisors.card : ℝ)) =O[atTop] fun k : ℕ => 1 / (Real.exp k - 1)

/-- **Prime-counting function from the smooth divisor count.** For a natural number $k$ let
$$\tilde\tau(k) = \sum_{j=1}^{k} \exp\left(-\frac{\pi^2}{2} k j^3 \sin^2\frac{k\pi}{j}\right),$$
and for $n \ge 2$ let $\tilde\pi(n) = \sum_{k=2}^{n} e^{-k(\tilde\tau(k) - 2)}$. Then for every
natural number $n \ge 2$, $|\tilde\pi(n) - \pi(n)| < 0.7129749140934$, where $\pi(n)$ is the
number of primes at most $n$.

The constant is $0.684 + 1/(e^3(e - 1))$ truncated to thirteen decimal places, the sum of the
two one-sided bounds, as the two-sided bound requires.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Theorem 2 (`integers-2026-A46-thm-2`). -/
public theorem_wanted primeCountingApprox_abs_sub_lt (n : ℕ) (hn : 2 ≤ n) :
    let τ' : ℕ → ℝ := fun k => ∑ j ∈ Icc 1 k,
      Real.exp (-(Real.pi ^ 2 / 2 * k * j ^ 3 * Real.sin (k * Real.pi / j) ^ 2))
    |∑ k ∈ Icc 2 n, Real.exp (-(k * (τ' k - 2))) - Nat.primeCounting n| < 0.7129749140934

/-- **Exponential approximation of the sum-of-divisors function.** Let $A$ be a real-valued
function of two natural numbers such that $A(k, n) \sin^2(n\pi/k) \ge 1$ for all natural numbers
$k, n$ with $1 \le k \le n$ and $k \nmid n$. For a natural number $n \ge 1$ let $\sigma(n)$
be the sum of the positive divisors of $n$ and
$$\tilde\sigma(n) = \sum_{k=1}^{n} k\, e^{-nkA(k, n)\sin^2(n\pi/k)}.$$
Then $\tilde\sigma(n) - \sigma(n) < \frac{n}{e^n - 1}$.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Theorem 3 (`integers-2026-A46-thm-3`). -/
public theorem_wanted divisorSumApprox_sub_lt (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, k * Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) -
        ∑ d ∈ n.divisors, (d : ℝ) < n / (Real.exp n - 1)

end

end MetaMathlibExt

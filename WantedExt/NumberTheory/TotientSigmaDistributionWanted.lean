/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace MetaMathlibExt

@[expose] public section

/-! # The distribution of `φ(σ(n))`

Statements from Dixit and Bhattacharjee on how often `φ(σ(n))` is large compared with `n`.
`log_k` is the `k`-fold iterated natural logarithm, written out with `Real.log`. Counts run
over positive integers `n ≤ x`, i.e. `n ∈ Finset.Icc 1 ⌊x⌋₊`. The paper's Lemma 2
(Siegel–Walfisz in prime-counting form) is already stated as
`MathlibExt.NumberTheory.PrimeCounting.UniformPrimeCountingWanted.uniform_prime_counting_arithmetic_progression`.
-/

open Filter Asymptotics

open Classical in
/-- **Pollack–Pomerance sieve bound.** There is an absolute constant $C > 0$ such that for every
set $P$ of primes and every real $x > 1$, the number of integers $n$ with $1 \le n \le x$ that
are divisible by no prime in $P$ is at most $C x \exp(-A_P(x))$, where
$A_P(x) = \sum_{p \in P,\ p \le x} 1/p$.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Lemma 1 (`integers-2024-A65-lem-1`), quoting Pollack and
Pomerance, Lemma 3. -/
public theorem_wanted card_free_of_prime_set_le_exp_neg_sum_inv :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Set ℕ), (∀ p ∈ P, p.Prime) → ∀ x : ℝ, 1 < x →
      ((((Finset.Icc 1 ⌊x⌋₊).filter fun n => ∀ p ∈ P, ¬ p ∣ n).card : ℕ) : ℝ) ≤
        C * x * Real.exp (-∑ p ∈ (Finset.Iic ⌊x⌋₊).filter (· ∈ P), (1 : ℝ) / p)

/-- **Integers whose sum of divisors is not divisible by $p$.** There is an absolute constant
$C > 0$ such that for every prime $p$ and every real $x \ge e^p$, the number of integers $n$ with
$1 \le n \le x$ for which $p$ does not divide the sum of divisors $\sigma(n)$ is at most
$C x (\log \log x / \log x)^{1/(p-1)}$.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Lemma 3 (`integers-2024-A65-lem-3`). -/
public theorem_wanted card_not_dvd_sigma_le :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∀ x : ℝ, Real.exp p ≤ x →
      ((((Finset.Icc 1 ⌊x⌋₊).filter fun n => ¬ p ∣ ArithmeticFunction.sigma 1 n).card : ℕ) :
          ℝ) ≤
        C * x * (Real.log (Real.log x) / Real.log x) ^ ((1 : ℝ) / ((p : ℝ) - 1))

/-- **Upper bound for the number of $n$ with $\varphi(\sigma(n)) \ge c n$.** Write $\log_k$ for
the $k$-fold iterated natural logarithm, so $\log_3 x = \log \log \log x$, and let $\varphi$ be
Euler's totient function and $\sigma$ the sum of divisors. For every real $c > 0$ there is a
constant $C$ such that for all sufficiently large $x$, the number of integers $n$ with
$1 \le n \le x$ and $\varphi(\sigma(n)) \ge c n$ is at most
$$
\frac{\pi^2 x}{6 c \log_4 x} +
C \, \frac{x \log_3 x}{(\log x)^{1/\log_3 x} \log_4 x}.
$$

The bound is only claimed for large $x$ since it needs $\log_4 x > 0$, that is, $x > e^{e^e}$.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Theorem 1 (`integers-2024-A65-thm-1`). -/
public theorem_wanted card_totient_sigma_ge_mul_le (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ᶠ x in atTop,
      ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
          c * n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ) ≤
        Real.pi ^ 2 * x / (6 * c * Real.log (Real.log (Real.log (Real.log x)))) +
          C * (x * Real.log (Real.log (Real.log x)) /
            (Real.log x ^ (1 / Real.log (Real.log (Real.log x))) *
              Real.log (Real.log (Real.log (Real.log x)))))

/-- **How often $\varphi(\sigma(n)) \ge n / f(n)$.** Write $\log_k$ for the $k$-fold iterated
natural logarithm, so $\log_3 x = \log \log \log x$, and let $\varphi$ be Euler's totient function
and $\sigma$ the sum of divisors. Let $f$ be a real function that is positive and non-decreasing
on $(0, \infty)$ with $f(x) = o(\log_4 x)$ as $x \to \infty$, and let $P_f(x)$ be the number of
integers $n$ with $1 \le n \le x$ and $\varphi(\sigma(n)) \ge n / f(n)$. Then, as $x \to \infty$,
$$
P_f(x) = O\left(\frac{x f(x)}{\log_4 x} +
\frac{x \log_3 x}{(\log x)^{1/\log_3 x} \log_4 x}\right)
$$
and $P_f(x) = o(x)$.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Theorem 2 (`integers-2024-A65-thm-2`). -/
public theorem_wanted card_totient_sigma_ge_div_isBigO (f : ℝ → ℝ)
    (hpos : ∀ x, 0 < x → 0 < f x) (hmono : MonotoneOn f (Set.Ioi 0))
    (hf : f =o[atTop] fun x => Real.log (Real.log (Real.log (Real.log x)))) :
    ((fun x : ℝ => ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / f n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ))
      =O[atTop] fun x =>
        x * f x / Real.log (Real.log (Real.log (Real.log x))) +
          x * Real.log (Real.log (Real.log x)) /
            (Real.log x ^ (1 / Real.log (Real.log (Real.log x))) *
              Real.log (Real.log (Real.log (Real.log x))))) ∧
    ((fun x : ℝ => ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / f n ≤ (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ))
      =o[atTop] fun x => x)

/-- **Exceptions to $\varphi(\sigma(n)) \le n / \log_5 n$.** Write $\log_k$ for the $k$-fold
iterated natural logarithm, and let $\varphi$ be Euler's totient function and $\sigma$ the sum of
divisors. The number of integers $n$ with $1 \le n \le x$ and $\varphi(\sigma(n)) > n / \log_5 n$
is $O(x \log_5 x / \log_4 x)$ as $x \to \infty$.

The finitely many small $n$ for which $\log_5 n$ is not a positive real are absorbed by the
$O$-term.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Corollary 1 (`integers-2024-A65-cor-1`). -/
public theorem_wanted card_totient_sigma_gt_div_log_five_isBigO :
    (fun x : ℝ => ((((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
        (n : ℝ) / Real.log (Real.log (Real.log (Real.log (Real.log n)))) <
          (Nat.totient (ArithmeticFunction.sigma 1 n) : ℝ)).card : ℕ) : ℝ))
      =O[atTop] fun x =>
        x * Real.log (Real.log (Real.log (Real.log (Real.log x)))) /
          Real.log (Real.log (Real.log (Real.log x)))

end

end MetaMathlibExt

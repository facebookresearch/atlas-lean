/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.MaxPrimeFac
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael

/-! # Largest prime factors of shifted primes

Statement-only requests for the shifted-prime inputs in Lebowitz-Lockard and Saunders' bound for
runs of integers with constant Carmichael function: the Baker–Harman lower bound on primes `p`
whose shift `p + a` has a large prime factor, and the resulting count of large primes `q`
dividing some `p - 1`. Throughout, `c = 0.677`.
-/

open Filter

namespace MetaMathlibExt

@[expose] public section

/-- **Baker–Harman: shifted primes with a large prime factor.** For every integer $a$ and every
real $\theta$ with $0 < \theta \le 0.677$ there is a real $\delta$ with $0 < \delta < 1$ such that,
for all sufficiently large real $x$, the number of primes $p \le x$ for which the largest prime
factor $P(|p + a|)$ of $|p + a|$ exceeds $x^\theta$ is greater than $\delta x / \log x$. Here
$P(0) = 0$ and $P(1) = 1$.

The statement covers every integer $a$, as the cited lemma is printed; Baker and Harman state the
bound for a nonzero shift, and the case $a = 0$ follows from the prime number theorem, since every
prime in $(x^\theta, x]$ qualifies and these number $(1 + o(1)) x / \log x$.

Source: Noah Lebowitz-Lockard and J.C. Saunders, *Runs of Integers with Constant Values of the
Carmichael Function*, INTEGERS 24 (2024), Article A91, Lemma 1 (`integers-2024-A91-lem-1`), quoted
there from Baker and Harman. -/
public theorem_wanted exists_card_maxPrimeFac_prime_add_gt_rpow (a : ℤ) {θ : ℝ} (hθ : 0 < θ)
    (hθc : θ ≤ 677 / 1000) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ x : ℝ in atTop,
      δ * x / Real.log x <
        (((Finset.range (⌊x⌋₊ + 1)).filter fun p : ℕ =>
          p.Prime ∧ x ^ θ < (Nat.maxPrimeFac ((p : ℤ) + a).natAbs : ℝ)).card : ℝ)

open scoped Classical in
/-- **Large prime divisors of shifted primes.** There is a real number $C > 0$ such that for all
sufficiently large real $x$ we have $x^{0.677} / \log x \le C \cdot N(x)$, where $N(x)$ is the
number of primes $q \le x$ with $q > x^{0.677}$ such that $q \mid p - 1$ for some prime $p \le x$.

The condition $q \le x$ is automatic, since $q \mid p - 1$ with $p \le x$ forces $q < x$.

Source: Noah Lebowitz-Lockard and J.C. Saunders, *Runs of Integers with Constant Values of the
Carmichael Function*, INTEGERS 24 (2024), Article A91, Lemma 2 (`integers-2024-A91-lem-2`). -/
public theorem_wanted exists_rpow_div_log_le_mul_card_prime_dvd_prime_sub_one :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      x ^ (677 / 1000 : ℝ) / Real.log x ≤
        C * (((Finset.range (⌊x⌋₊ + 1)).filter fun q : ℕ =>
          q.Prime ∧ x ^ (677 / 1000 : ℝ) < q ∧
            ∃ p ∈ Finset.range (⌊x⌋₊ + 1), p.Prime ∧ p % q = 1).card : ℝ)

/-- **Runs of constant Carmichael values.** For real $x$, let $F_\lambda(x)$ be the largest natural
number $k$ for which there is a natural number $n \ge 0$ with $n + k \le x$ and
$\lambda(n + 1) = \lambda(n + 2) = \cdots = \lambda(n + k)$ (and $0$ if there is no such $k$), where
$\lambda$ is the Carmichael function. Then $F_\lambda(x) = O\left((\log x)^{1000/677}\right)$ as
$x \to \infty$; that is, $F_\lambda(x) = O\left((\log x)^{1/c}\right)$ with $c = 0.677$.

This follows the definition of $F_f(x)$ in the arXiv version (arXiv:2402.06832v4, Section 1):
$F_f(x)$ is the largest $k$ for which $f(n+1) = \cdots = f(n+k)$ has a solution with $n + k \le x$.

Source: Noah Lebowitz-Lockard and J.C. Saunders, *Runs of Integers with Constant Values of the
Carmichael Function*, INTEGERS 24 (2024), Article A91, Theorem 3 (`integers-2024-A91-thm-3`). -/
public theorem_wanted carmichael_constant_run_length_isBigO :
    (fun x : ℝ => ((sSup {k : ℕ | ∃ n : ℕ, ((n + k : ℕ) : ℝ) ≤ x ∧
        ∀ i ∈ Finset.Icc 1 k, ArithmeticFunction.carmichael (n + i) =
          ArithmeticFunction.carmichael (n + 1)} : ℕ) : ℝ)) =O[atTop]
      fun x : ℝ => Real.log x ^ ((1000 : ℝ) / 677)


/-- **Pollack–Pomerance–Treviño: nonincreasing runs of Euler's function.** For real $x$, let
$G_\varphi(x)$ be the largest natural number $k$ for which there is a natural number $n \ge 0$ with
$n + k \le x$ and $\varphi(n + 1) \ge \varphi(n + 2) \ge \cdots \ge \varphi(n + k)$ (and $0$ if
there is no such $k$), where $\varphi$ is Euler's totient function. Then
$G_\varphi(x) \sim \log_3 x / \log_6 x$ as $x \to \infty$, where $\log_j$ denotes the $j$-fold
iterate of the natural logarithm.

This follows the definition of $G_f(x)$ in the paper (arXiv:2402.06832v4, Section 1): $G_f(x)$ is
the largest $k$ for which $f(n+1) \ge f(n+2) \ge \cdots \ge f(n+k)$ has a solution with
$n + k \le x$.

Source: Noah Lebowitz-Lockard and J.C. Saunders, *Runs of Integers with Constant Values of the
Carmichael Function*, INTEGERS 24 (2024), Article A91, Theorem 1 (`integers-2024-A91-thm-1`),
quoted there from Pollack, Pomerance, and Treviño. -/
public theorem_wanted totient_nonincreasing_run_length_isEquivalent :
    Asymptotics.IsEquivalent atTop
      (fun x : ℝ => ((sSup {k : ℕ | ∃ n : ℕ, ((n + k : ℕ) : ℝ) ≤ x ∧
        ∀ i ∈ Finset.Ico 1 k, Nat.totient (n + i + 1) ≤ Nat.totient (n + i)} : ℕ) : ℝ))
      fun x : ℝ => Real.log^[3] x / Real.log^[6] x

end

end MetaMathlibExt

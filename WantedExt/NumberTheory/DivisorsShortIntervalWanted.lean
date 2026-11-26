/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.Algebra.BigOperators.PrefixSumReordering
public import MathlibExt.NumberTheory.CohenLcmGcd
public import MathlibExt.NumberTheory.DivisorsShortInterval
public import MathlibExt.NumberTheory.DivisorsShortIntervalCardUnsolvableSqAddPrimePow
public import MathlibExt.NumberTheory.DivisorsShortIntervalExistsShortIntervalDivisorCountLeOfWindowThetaSq

namespace MetaMathlibExt

@[expose] public section

/-! Definitions follow the arXiv version of the paper (arXiv:2503.12146v1), which states
`D_n`, Conjecture 2, `V(n)` and `ξ(θ, η)` explicitly. Implied constants of `≪` and `≫` are
absolute: every dependence on `θ`, `η` and `ε` is displayed in the paper's bounds. Corollary 1
and Proposition 5 appear only in the journal version (INTEGERS 26 (2026), A115, PDF) and are
taken from it. -/

/-- **Arithmetic large sieve with prime-power moduli.** Let $N \ge 1$ be an integer and let $M$
be a finite set of integers contained in $[a, a + N)$ for some integer $a$. Let $S$ be a finite
set of primes and, for each $p \in S$, let $\beta_p \ge 1$ be an integer and let $\Omega_p$ be a
set of fewer than $p^{\beta_p}$ integers in $[0, p^{\beta_p})$ such that no $m \in M$ has its
remainder modulo $p^{\beta_p}$ in $\Omega_p$. Then for every real $Q \ge 1$,
$$|M| \le \frac{N + Q^2}{\sum_{1 \le q \le Q} h(q)},$$
where $q$ runs over the integers in $[1, Q]$ and $h(q) = \prod_{p \mid q} h_p(q)$, the product
over the prime factors $p$ of $q$ of $h_p(q) = |\Omega_p| / (p^{\beta_p} - |\Omega_p|)$ if
$p \in S$ and $p^{\beta_p}$ exactly divides $q$, and $h_p(q) = 0$ otherwise (so $h(1) = 1$).

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 3 (`integers-2026-A115-lem-3`). -/
public theorem_wanted card_le_of_avoids_residues_primePow (M : Finset ℤ) (N : ℕ) (hN : 1 ≤ N)
    (a : ℤ) (hM : ∀ m ∈ M, a ≤ m ∧ m < a + N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (β : ℕ → ℕ) (hβ : ∀ p ∈ S, 1 ≤ β p) (Ω : ℕ → Finset ℤ)
    (hΩ : ∀ p ∈ S, ∀ c ∈ Ω p, 0 ≤ c ∧ c < (p : ℤ) ^ β p)
    (hΩcard : ∀ p ∈ S, (Ω p).card < p ^ β p)
    (havoid : ∀ p ∈ S, ∀ m ∈ M, m % (p : ℤ) ^ β p ∉ Ω p) (Q : ℝ) (hQ : 1 ≤ Q) :
    (M.card : ℝ) ≤ (N + Q ^ 2) /
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∏ p ∈ q.primeFactors,
        (if p ∈ S ∧ q.factorization p = β p then
          ((Ω p).card : ℝ) / ((p : ℝ) ^ β p - (Ω p).card) else 0)

/-- **Letendre's bound for divisors in short intervals.** For a natural number $n$ and real numbers
$X$, $Y$, let $D_n(X, Y)$ be the number of divisors $d$ of $n$ with $X \le d \le X + Y$, let
$\tau(n)$ be the number of divisors of $n$, let $V(n)$ be the largest exponent in the prime
factorization of $n$, and let $\xi(\theta, \eta)$ be Letendre's saving exponent. There is an
absolute constant $C$ such that for all real numbers $\theta$, $\eta$ with $0 < \eta < \theta < 1$
and every integer $n \ge 2$,
$D_n(n^\theta, n^\eta) \le C \tau(n)^{1 - \xi(\theta, \eta)} V(n) \log \tau(n) /
(\theta(1 - \theta))$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1 (`integers-2026-A115-thm-1`). -/
public theorem_wanted exists_shortIntervalDivisorCount_le_letendre :
    ∃ C : ℝ, ∀ θ η : ℝ, 0 < η → η < θ → θ < 1 → ∀ n : ℕ, 2 ≤ n →
      (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ η) : ℝ) ≤
        C * (n.divisors.card : ℝ) ^ (1 - letendreXi θ η) *
          ((n.primeFactors.sup n.factorization : ℕ) * Real.log n.divisors.card /
            (θ * (1 - θ)))

/-- **Lower bound for constants bounding divisors in short windows.** There is an absolute
constant $c > 0$ with the following property. Let $\theta$, $\varepsilon$ and $k$ be real numbers
with $0 < \theta < 1$ and $0 < \varepsilon < \theta$, and suppose that for every integer $n \ge 1$
the number of divisors $d$ of $n$ with $n^\theta \le d \le n^\theta + n^{\theta - \varepsilon}$ is
at most $k$. Then $c \sqrt{\varepsilon} \, (\theta(1 - \theta))^{3/2} \,
\left(1 / (\theta^\theta (1 - \theta)^{1 - \theta})\right)^{1/\varepsilon} \le k$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 2 (`integers-2026-A115-thm-2`). -/
public theorem_wanted exists_lower_bound_conjecture_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ε k : ℝ, 0 < θ → θ < 1 → 0 < ε → ε < θ →
      (∀ n : ℕ, 1 ≤ n →
        (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ - ε)) : ℝ) ≤ k) →
      c * Real.sqrt ε * (θ * (1 - θ)) ^ (3 / 2 : ℝ) *
          (1 / (θ ^ θ * (1 - θ) ^ (1 - θ))) ^ (1 / ε) ≤ k


/-- **Letendre's square-root bound for divisors in short intervals.** For a natural number $n$
and real numbers $X$, $Y$, let $D_n(X, Y)$ be the number of divisors $d$ of $n$ with
$X \le d \le X + Y$, let $\tau(n)$ be the number of divisors of $n$, and let $\xi(\theta, \eta)$
be Letendre's saving exponent. There is an absolute constant $C$ such that for all real numbers
$\theta$, $\eta$ with $0 < \eta < \theta < 1$ and every integer $n \ge 2$,
$D_n(n^\theta, n^\eta) \le C \tau(n)^{1 - \xi(\theta, \eta)/2}
\sqrt{\log \tau(n) / (\theta(1 - \theta))}$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Corollary 1 (`integers-2026-A115-cor-1`, journal version). -/
public theorem_wanted exists_shortIntervalDivisorCount_le_sqrt_letendre :
    ∃ C : ℝ, ∀ θ η : ℝ, 0 < η → η < θ → θ < 1 → ∀ n : ℕ, 2 ≤ n →
      (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ η) : ℝ) ≤
        C * (n.divisors.card : ℝ) ^ (1 - letendreXi θ η / 2) *
          Real.sqrt (Real.log n.divisors.card / (θ * (1 - θ)))

/-- **Divisors near $\sqrt{an/b}$.** Let $a$ and $b$ be coprime positive integers. For a natural
number $n$ and real numbers $X$, $Y$, let $D_n(X, Y)$ be the number of divisors $d$ of $n$ with
$X \le d \le X + Y$, and let $\omega(m)$ be the number of distinct prime factors of $m$. There is
a constant $C$, depending on $a$ and $b$, such that for all integers $n \ge 1$ and $i \ge 1$,
writing $x_0 = \sqrt{an/b}$ and $w = \omega(4abn)$,
$$D_n\bigl(x_0, \sqrt{i x_0 / b}\bigr) \le C \min\bigl(i, \; i/w + w (\log w)^2\bigr).$$

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 5 (`integers-2026-A115-prop-5`, journal version). -/
public theorem_wanted exists_shortIntervalDivisorCount_sqrt_window_le (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 1 ≤ i →
      (shortIntervalDivisorCount n (Real.sqrt (a * n / b))
          (Real.sqrt (i * Real.sqrt (a * n / b) / b)) : ℝ) ≤
        C * min (i : ℝ) (i / (4 * a * b * n).primeFactors.card +
          (4 * a * b * n).primeFactors.card * Real.log (4 * a * b * n).primeFactors.card ^ 2)

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.Radical.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import MathlibExt.NumberTheory.Bernoulli.OddRadical
public import MathlibExt.NumberTheory.Bernoulli.PolynomialDenominatorRadical

namespace MetaMathlibExt

@[expose] public section

open Polynomial UniqueFactorizationMonoid

/-- **Product formula for the denominator of $B_n(x) - B_n$.** Let $n \ge 1$, let $B_n(x)$ be
the $n$-th Bernoulli polynomial and $B_n = B_n(0)$ the $n$-th Bernoulli number, and write
$s_p(n)$ for the sum of the base-$p$ digits of $n$. Then $\mathbb{D}_n$, the product of the
primes $p$ with $s_p(n) \ge p$, equals the denominator of the polynomial $B_n(x) - B_n$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2,
definition of `𝔻_n` and equation (2.3), quoting Kellner (2017), Section 5. -/
public theorem_wanted bernoulliDiffDenominator_eq_polynomialDenominator (n : ℕ) (hn : 1 ≤ n) :
    bernoulliDiffDenominator n =
      polynomialDenominator (Polynomial.bernoulli n - C (_root_.bernoulli n))

/-- **Kellner's large-prime conjectures imply the Bernoulli derivative conjectures.** For
$n \in \mathbb{N}$ let $\mathbb{D}^{+}_n$ be the product of the primes $p > \sqrt{n}$ whose
base-$p$ digit sum $s_p(n)$ satisfies $s_p(n) \ge p$, let $\omega(m)$ be the number of distinct
prime factors of $m$, and let $\overline{\mathcal{S}}$ be the set of $n \ge 1$ such that the
derivative $B_n'(x)$ of the Bernoulli polynomial $B_n(x)$ has integer coefficients. If
$\mathbb{D}^{+}_n > 1$ for every $n > 192$, then
$\overline{\mathcal{S}} = \{1, 2, 4, 6, 10, 12, 28, 30, 36, 60\}$. If there is a real number
$\kappa > 1$ with $\omega(\mathbb{D}^{+}_n) \sim \kappa \sqrt{n} / \log n$ as $n \to \infty$, then
$\overline{\mathcal{S}}$ is finite.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 3
(`jis-2024-24.2.8-thm-3`). -/
public theorem_wanted kellner_conjectures_imply_bernoulli_integral_derivative_conjectures :
    (KellnerLargePartConjecture →
      bernoulliIntegralDerivativeIndices 1 = {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}) ∧
    (KellnerLargePartAsymptoticConjecture → (bernoulliIntegralDerivativeIndices 1).Finite)

/-- **Bordellès–Luca–Moree–Shparlinski asymptotic and finiteness of integral derivatives.** For
$n \in \mathbb{N}$ let $\mathbb{D}^{+}_n$ be the product of the primes $p > \sqrt{n}$ whose
base-$p$ digit sum $s_p(n)$ satisfies $s_p(n) \ge p$, and let $\omega(m)$ be the number of
distinct prime factors of $m$. There is a real number $\kappa > 1$ with
$\omega(\mathbb{D}^{+}_n) \sim \kappa \sqrt{n} / \log n$ as $n \to \infty$, and the set of
$n \ge 1$ such that the derivative $B_n'(x)$ of the Bernoulli polynomial $B_n(x)$ has integer
coefficients is finite.

Bordellès, Luca, Moree and Shparlinski prove the asymptotic with $\kappa = 2$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Corollary 4, quoting
Bordellès, Luca, Moree, and Shparlinski (2018), Corollary 1.6 (`jis-2024-24.2.8-cor-4`). -/
public theorem_wanted kellnerLargePartAsymptoticConjecture_and_finite_integral_derivative :
    KellnerLargePartAsymptoticConjecture ∧ (bernoulliIntegralDerivativeIndices 1).Finite

/-- **Constraints on Bernoulli polynomials with integral derivative.** Let $n \ge 1$ be such that
the derivative $B_n'(x)$ of the Bernoulli polynomial $B_n(x)$ has integer coefficients. Then
$n + 1$ is prime, and if $n \notin \{1, 2, 4, 6, 10, 12, 28, 30, 36, 60\}$, then $n > 10^7$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 5
(`jis-2024-24.2.8-thm-5`). -/
public theorem_wanted bernoulli_integral_derivative_succ_prime_and_large :
    (∀ n ∈ bernoulliIntegralDerivativeIndices 1, (n + 1).Prime) ∧
    ∀ n ∈ bernoulliIntegralDerivativeIndices 1,
      n ∉ ({1, 2, 4, 6, 10, 12, 28, 30, 36, 60} : Set ℕ) → 10 ^ 7 < n

/-- **Integrality of the derivative of a Bernoulli polynomial.** Let $n \ge 1$, let $B_m(x)$
denote the $m$-th Bernoulli polynomial, write $s_p(n)$ for the sum of the base-$p$ digits of $n$,
and let $\mathbb{D}^\perp_n$ be the product of the primes $p$ with $p \nmid n$ and
$s_p(n) \ge p$. Then $B_n'(x)$ has integer coefficients if and only if $\mathbb{D}^\perp_n = 1$,
and $\mathbb{D}^\perp_n = 1$ if and only if the denominator of $B_{n-1}(x)$ equals the radical
$\operatorname{rad}(n)$. Moreover, if $B_n'(x)$ has integer coefficients, then $n + 1$ is prime.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 9
(`jis-2024-24.2.8-thm-9`). -/
public theorem_wanted bernoulli_derivative_integral_iff (n : ℕ) (hn : 1 ≤ n) :
    (n ∈ bernoulliIntegralDerivativeIndices 1 ↔ bernoulliDiffDenominatorCoprimePart n = 1) ∧
    (bernoulliDiffDenominatorCoprimePart n = 1 ↔
      polynomialDenominator (Polynomial.bernoulli (n - 1)) = radical n) ∧
    (n ∈ bernoulliIntegralDerivativeIndices 1 → (n + 1).Prime)

/-- **Indices with $\mathbb{D}_n = \operatorname{rad}(n + 1)$.** Write $s_p(m)$ for the sum of
the base-$p$ digits of $m$, let $\mathbb{D}_m$ be the product of the primes $p$ with
$s_p(m) \ge p$, and let $\mathbb{D}^\perp_m$ be the product of the primes $p$ with $p \nmid m$
and $s_p(m) \ge p$. Let $\overline{\mathcal{R}}$ be the set of $n \ge 1$ with
$\mathbb{D}_n = \operatorname{rad}(n + 1)$, where $\operatorname{rad}$ denotes the radical. For
every $n \in \overline{\mathcal{R}}$, the number $n + 1$ is not prime; if $n$ is odd then
$\mathbb{D}^\perp_{n+1} = 1$; and if $n$ is even then $n = 2^e$ for some $e \ge 1$. Moreover,
the set $\overline{\mathcal{R}}$ is finite.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 10
(`jis-2024-24.2.8-thm-10`). -/
public theorem_wanted bernoulliDiffDenominator_eq_radical_succ_properties :
    (∀ n : ℕ, 1 ≤ n → bernoulliDiffDenominator n = radical (n + 1) →
      ¬ (n + 1).Prime ∧
      (Odd n → bernoulliDiffDenominatorCoprimePart (n + 1) = 1) ∧
      (Even n → ∃ e, 1 ≤ e ∧ n = 2 ^ e)) ∧
    {n : ℕ | 1 ≤ n ∧ bernoulliDiffDenominator n = radical (n + 1)}.Finite

/-- **Denominators of higher derivatives of Bernoulli polynomials.** For $m \ge 0$ let
$\mathfrak{D}_m$ be the denominator of the Bernoulli polynomial $B_m(x)$, and for $k \ge 1$ let
$\mathfrak{D}_n^{(k)}$ be the denominator of the $k$-th derivative $B_n^{(k)}(x)$ of $B_n(x)$.
Write $(n)_k = n(n-1)\cdots(n-k+1)$ for the falling factorial, $s_p(m)$ for the sum of the
base-$p$ digits of $m$, $\operatorname{rad}(n)$ for the product of the primes dividing $n$, and
$\mathbb{D}^{\perp}_m$ for the product of the primes $p \nmid m$ with $s_p(m) \ge p$. Let
$k, n \ge 1$. If $k \le n$, then

$$\mathfrak{D}_n^{(k)} = \frac{\mathfrak{D}_{n-k}}{\gcd(\mathfrak{D}_{n-k}, (n)_k)}
= \frac{\mathbb{D}^{\perp}_{n-k+1}}{\gcd(\mathbb{D}^{\perp}_{n-k+1}, (n)_{k-1})}
= \prod_{p \text{ prime},\ p \le n,\ p \nmid (n)_k,\ s_p(n-k+1) \ge p} p.$$

If $n < k$, then $\mathfrak{D}_n^{(k)} = 1$. No prime $p \le k$ divides $\mathfrak{D}_n^{(k)}$.
Finally, $\mathfrak{D}_n^{(1)} = \mathfrak{D}_{n-1} / \operatorname{rad}(n) = \mathbb{D}^{\perp}_n$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 13
(`jis-2024-24.2.8-thm-13`). -/
public theorem_wanted bernoulli_higher_derivative_denominator (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (k ≤ n →
      polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) =
          polynomialDenominator (Polynomial.bernoulli (n - k)) /
            Nat.gcd (polynomialDenominator (Polynomial.bernoulli (n - k))) (n.descFactorial k) ∧
        polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) =
          bernoulliDiffDenominatorCoprimePart (n - k + 1) /
            Nat.gcd (bernoulliDiffDenominatorCoprimePart (n - k + 1)) (n.descFactorial (k - 1)) ∧
        polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) =
          ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ n.descFactorial k ∧
            p ≤ (Nat.digits p (n - k + 1)).sum), p) ∧
    (n < k → polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) = 1) ∧
    (∀ p : ℕ, p.Prime → p ≤ k →
      ¬ p ∣ polynomialDenominator (derivative^[k] (Polynomial.bernoulli n))) ∧
    (k = 1 →
      polynomialDenominator (derivative (Polynomial.bernoulli n)) =
          polynomialDenominator (Polynomial.bernoulli (n - 1)) / radical n ∧
        polynomialDenominator (derivative (Polynomial.bernoulli n)) =
          bernoulliDiffDenominatorCoprimePart n)

/-- **Finitely many Bernoulli polynomials have an integral $k$-th derivative.** For $k \ge 1$ let
$\overline{\mathcal{S}}_k$ be the set of $n \ge 1$ such that the $k$-th derivative $B_n^{(k)}(x)$
of the Bernoulli polynomial $B_n(x)$ has integer coefficients. For every $k \ge 1$ the set
$\overline{\mathcal{S}}_k$ is finite and
$\overline{\mathcal{S}}_k \subseteq \overline{\mathcal{S}}_{k+1}$.

The paper writes $\subset$ for this inclusion; its proof gives inclusion, not strict inclusion.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 14
(`jis-2024-24.2.8-thm-14`). -/
public theorem_wanted bernoulliIntegralDerivativeIndices_finite_and_mono :
    (∀ k : ℕ, 1 ≤ k → (bernoulliIntegralDerivativeIndices k).Finite) ∧
    ∀ k : ℕ, 1 ≤ k →
      bernoulliIntegralDerivativeIndices k ⊆ bernoulliIntegralDerivativeIndices (k + 1)

/-- **Parity, radical divisibility and an lcm recursion for $\mathbb{D}_n$.** Write $s_p(m)$ for
the sum of the base-$p$ digits of $m$, let $\mathbb{D}_m$ be the product of the primes $p$ with
$s_p(m) \ge p$, and let $\mathbb{D}^\perp_m$ be the product of the primes $p$ with $p \nmid m$
and $s_p(m) \ge p$. Let $n \ge 1$. Then $\mathbb{D}_n$ is odd if and only if $n = 2^e$ for some
$e \ge 0$. If $n + 1$ is not prime, then the radical $\operatorname{rad}(n + 1)$ divides both
$\mathbb{D}_n$ and $\mathbb{D}^\perp_n$. If $n \ge 3$ is odd, then
$\mathbb{D}_n = \operatorname{lcm}(\mathbb{D}_{n+1}, \operatorname{rad}(n + 1))$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Lemma 16
(`jis-2024-24.2.8-lem-16`). -/
public theorem_wanted bernoulliDiffDenominator_parity_radical_lcm (n : ℕ) (hn : 1 ≤ n) :
    (Odd (bernoulliDiffDenominator n) ↔ ∃ e, n = 2 ^ e) ∧
    (¬ (n + 1).Prime → radical (n + 1) ∣ bernoulliDiffDenominator n ∧
      radical (n + 1) ∣ bernoulliDiffDenominatorCoprimePart n) ∧
    (3 ≤ n → Odd n →
      bernoulliDiffDenominator n = Nat.lcm (bernoulliDiffDenominator (n + 1)) (radical (n + 1)))

/-- **$\mathbb{D}^+_n$ eventually exceeds every fixed rising product.** Write $s_p(n)$ for the sum
of the base-$p$ digits of $n$ and let $\mathbb{D}^+_n$ be the product of the primes $p$ with
$p^2 > n$ and $s_p(n) \ge p$. For every $k \ge 1$ there is $N$ such that
$\mathbb{D}^+_n > (n + 1)(n + 2) \cdots (n + k)$ for all $n > N$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Lemma 18
(`jis-2024-24.2.8-lem-18`). -/
public theorem_wanted bernoulliDiffDenominatorLargePart_eventually_gt_descFactorial (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n, N < n → (n + k).descFactorial k < bernoulliDiffDenominatorLargePart n

end

end MetaMathlibExt

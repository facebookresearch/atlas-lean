/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.Analysis.SpecialFunctions.Exp.Zelinsky
public import MathlibExt.Analysis.SpecialFunctions.Log.Zelinsky
public import MathlibExt.NumberTheory.ArithmeticFunction.AbundancySupDivIndex
public import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeProduct
public import MathlibExt.NumberTheory.EulerPrime
public import WantedExt.NumberTheory.PrimitiveNondeficientWanted
public import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectAbundancySurplus
public import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum
public import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSumNotIsEulerPrimeOfMod165Eq
public import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSumPrimitiveNondeficientPrimeReciprocalSumGe

/-! # Prime reciprocal sums of odd perfect and primitive non-deficient numbers

Statement-only requests from Joshua Zelinsky, *The Sum of the Reciprocals of the Prime
Divisors of an Odd Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025),
Article A59 (arXiv:2402.14234v5). The paper writes `T(n) = ∑_{p ∣ n} 1/p`, spelled out
below as `∑ p ∈ n.primeFactors, (1 : ℝ) / p`; `H(n) = ∏_{p ∣ n} p/(p-1)` is
`abundancySup`, `h(n) = σ(n)/n` is `abundancyIndex`, and the surplus of a non-deficient
`n` is `S(n) = H(n) - 2`. Non-deficient and primitive non-deficient are
`IsNondeficient` and `IsPrimitiveNondeficient`; the paper's least prime factor `p₁` is
`n.minFac`. An odd perfect number is `Odd n ∧ n.Perfect`, and Euler's form with special
prime `q` is `EulerianForm`.
-/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Zelinsky's upper bound on the prime reciprocal sum of an odd perfect number.** Let $n$ be an
odd perfect number whose least prime factor $p_1$ satisfies $p_1 \ge 11$, and let
$T(n) = \sum_{p \mid n} 1/p$, the sum over the primes $p$ dividing $n$. Then
$T(n) < \log 2 - \frac{11}{50 p_1^2}$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Corollary 1 (`integers-2025-A59-cor-1`). -/
public theorem_wanted oddPerfect_primeReciprocalSum_lt_log_two_sub
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h11 : 11 ≤ n.minFac) :
    ∑ p ∈ n.primeFactors, (1 : ℝ) / p < Real.log 2 - 11 / (50 * (n.minFac : ℝ) ^ 2)

/-- **Lower bound for the prime-counting function at primes $p \ge 19$.** For every prime
$p \ge 19$, the number $\pi(p)$ of primes at most $p$ satisfies $\pi(p) \ge p/\log p + 1$,
where $\log$ is the natural logarithm.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 4 (`integers-2025-A59-lem-4`). -/
public theorem_wanted div_log_add_one_le_primeCounting
    (p : ℕ) (hp : p.Prime) (h19 : 19 ≤ p) :
    (p : ℝ) / Real.log p + 1 ≤ Nat.primeCounting p

/-- **Tail bound for the sum of $1/p^2$ over primes.** Let $q \ge 3$ be a prime and let
$M(q) = \sum_{p \ge q} 1/p^2$ be the sum over all primes $p \ge q$. Then
$M(q) < \frac{1}{q \log q}\left(1 + \frac{2 \log \log q}{\log q}\right)$,
where $\log$ is the natural logarithm.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 6 (`integers-2025-A59-lem-6`). -/
public theorem_wanted tsum_one_div_sq_primes_ge_lt
    (q : ℕ) (hq : q.Prime) (h3 : 3 ≤ q) :
    ∑' p : {p : ℕ // p.Prime ∧ q ≤ p}, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 <
      1 / ((q : ℝ) * Real.log q) * (1 + 2 * Real.log (Real.log q) / Real.log q)

/-- **Bound on the tail of the prime product of $p^2/(p^2-1)$.** Let $q$ be an odd prime. Then
$\sum_{p \ge q} \log \frac{p^2}{p^2-1} \le
\frac{1}{q \log q}\left(1 + \frac{2 \log \log q}{\log q}\right) + \frac{4}{q^3}$,
where the sum runs over the primes $p \ge q$. Equivalently, $\log E$ is at most this bound,
where $E = \prod_{p \ge q} \frac{p^2}{p^2-1}$ is the product over the primes $p \ge q$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 7 (`integers-2025-A59-lem-7`). -/
public theorem_wanted tsum_log_sq_div_sq_sub_one_primes_ge_le
    (q : ℕ) (hq : q.Prime) (hodd : Odd q) :
    ∑' p : {p : ℕ // p.Prime ∧ q ≤ p},
        Real.log (((p : ℕ) : ℝ) ^ 2 / (((p : ℕ) : ℝ) ^ 2 - 1)) ≤
      1 / ((q : ℝ) * Real.log q) * (1 + 2 * Real.log (Real.log q) / Real.log q) +
        4 / (q : ℝ) ^ 3

/-- **Odd perfect numbers divisible by 165 contain 5 exactly once.** If $n$ is an odd perfect
number divisible by $165$, then $5$ divides $n$ exactly once: $5 \mid n$ but $25 \nmid n$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 11 (`integers-2025-A59-lem-11`). -/
public theorem_wanted oddPerfect_factorization_five_eq_one_of_dvd
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h165 : 165 ∣ n) :
    n.factorization 5 = 1

/-- **Cohen–Hagis–Suryanarayana bounds on the prime reciprocal sum of an odd perfect number.**
Let $n$ be an odd perfect number and $T(n) = \sum_{p \mid n} 1/p$, the sum over the primes $p$
dividing $n$. If $\gcd(15, n) = 1$ then $T(n) \le 0.693148$; if $\gcd(15, n) = 3$ then
$T(n) \le 0.657304$; if $\gcd(15, n) = 5$ then $T(n) \le 0.678036$; and if $\gcd(15, n) = 15$
then $T(n) \le 0.673770$.

The source table also gives lower bounds, which are not stated here.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 1, Table 1 (`integers-2025-A59-prop-1`). -/
public theorem_wanted oddPerfect_primeReciprocalSum_le_of_gcd_fifteen
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) :
    (Nat.gcd 15 n = 1 → ∑ p ∈ n.primeFactors, (1 : ℝ) / p ≤ 0.693148) ∧
      (Nat.gcd 15 n = 3 → ∑ p ∈ n.primeFactors, (1 : ℝ) / p ≤ 0.657304) ∧
      (Nat.gcd 15 n = 5 → ∑ p ∈ n.primeFactors, (1 : ℝ) / p ≤ 0.678036) ∧
      (Nat.gcd 15 n = 15 → ∑ p ∈ n.primeFactors, (1 : ℝ) / p ≤ 0.673770)

/-- **Suryanarayana's bounds on the prime product of an odd perfect number.** Let $n$ be an odd
perfect number and $H(n) = \prod_{p \mid n} p/(p-1)$, the product over the primes $p$ dividing $n$.
If $\gcd(15, n) = 1$ then $H(n) \le 2.014754$; if $\gcd(15, n) = 3$ then $H(n) \le 2.096234$;
if $\gcd(15, n) = 5$ then $H(n) \le 2.031002$; and if $\gcd(15, n) = 15$ then
$H(n) \le 2.165439$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 2, Table 2 (`integers-2025-A59-prop-2`). -/
public theorem_wanted oddPerfect_abundancySup_le_of_gcd_fifteen
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) :
    (Nat.gcd 15 n = 1 → abundancySup n ≤ 2.014754) ∧
      (Nat.gcd 15 n = 3 → abundancySup n ≤ 2.096234) ∧
      (Nat.gcd 15 n = 5 → abundancySup n ≤ 2.031002) ∧
      (Nat.gcd 15 n = 15 → abundancySup n ≤ 2.165439)

/-- **Upper bound on the prime reciprocal sum of a primitive non-deficient number with one odd
exponent.** Let $n$ be a primitive non-deficient number with least prime factor $p_1 \ge 11$,
and let $t$ be a prime factor of $n$ such that the exponent of $t$ in $n$ is odd and the exponent
of every other prime factor of $n$ is even. Suppose $2 p_1 \le t + 2$, and let
$T(n) = \sum_{p \mid n} 1/p$, the sum over the primes $p$ dividing $n$. Then
$T(n) < \log 2 - \frac{11}{50 p_1^2}$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 4 (`integers-2025-A59-prop-4`). -/
public theorem_wanted primitiveNondeficient_primeReciprocalSum_lt_of_single_odd_exponent
    (n t : ℕ) (hn : IsPrimitiveNondeficient n) (ht : t ∈ n.primeFactors)
    (htodd : Odd (n.factorization t))
    (heven : ∀ p ∈ n.primeFactors, p ≠ t → Even (n.factorization p))
    (h11 : 11 ≤ n.minFac) (hpt : 2 * n.minFac ≤ t + 2) :
    ∑ p ∈ n.primeFactors, (1 : ℝ) / p < Real.log 2 - 11 / (50 * (n.minFac : ℝ) ^ 2)

/-- **Lower bound on the prime reciprocal sum of an odd primitive non-deficient number.** Let $n$
be an odd primitive non-deficient number with least prime factor $p_1$, let
$T(n) = \sum_{p \mid n} 1/p$ and $H(n) = \prod_{p \mid n} p/(p-1)$, with the sum and product over
the primes $p$ dividing $n$, and let $S = H(n) - 2$ be the surplus of $n$. Then
$T(n) \ge \log 2 - \frac{25}{32 p_1 \log p_1}
\left(1 + \frac{2 \log \log p_1}{\log p_1}\right) + \frac{S}{2} - \frac{S^2}{4}$.

The hypothesis that $n$ is odd is added: the statement as printed fails at $n = 6$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 7 (`integers-2025-A59-prop-7`). -/
public theorem_wanted odd_primitiveNondeficient_primeReciprocalSum_ge
    (n : ℕ) (hodd : Odd n) (hn : IsPrimitiveNondeficient n) :
    Real.log 2 -
          25 / (32 * (n.minFac : ℝ) * Real.log n.minFac) *
            (1 + 2 * Real.log (Real.log n.minFac) / Real.log n.minFac) +
        ((abundancySup n : ℝ) - 2) / 2 - ((abundancySup n : ℝ) - 2) ^ 2 / 4 ≤
      ∑ p ∈ n.primeFactors, (1 : ℝ) / p

/-- **Refined fifth-power bound on the Euler prime of an odd perfect number.** If $(n, q, e, m)$
is in Eulerian form, that is, $n$ is an odd perfect number, $q$ is a prime coprime to $m$,
$n = q^e m^2$ and $q \equiv e \equiv 1 \pmod 4$, then $e = 1$ or
$3^2 \cdot 5^2 \cdot 11^2 \cdot 13^2 \cdot q^5 < 2m^2$, that is,
$q < \left(2/(3^2 \cdot 5^2 \cdot 11^2 \cdot 13^2)\right)^{1/5} m^{2/5}$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 12 (`integers-2025-A59-prop-12`). -/
public theorem_wanted eulerianForm_exponent_eq_one_or_mul_pow_five_lt
    (n q e m : ℕ) (h : EulerianForm n q e m) :
    e = 1 ∨ 3 ^ 2 * 5 ^ 2 * 11 ^ 2 * 13 ^ 2 * q ^ 5 < 2 * m ^ 2

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalized Zumkeller numbers

Statements from Jayanta Kalita and Helen K. Saikia, "A Study on Generalized
Zumkeller Numbers", *INTEGERS* 24 (2024), Article A95.

`n` is *s-Zumkeller* when its proper divisors split into two parts with equal
sums of squares (`IsSZumkeller`), and *unitary s-Zumkeller* when its proper
unitary divisors (MathlibExt's `Nat.unitaryDivisors n` without `n`) do
(`IsUnitarySZumkeller`). Both parts are required to be nonempty, as in a
partition `{A, B}`; this only excludes `n = 1`, whose empty divisor set would
otherwise split trivially (and would contradict Proposition 13).

`σ₂(n)` is `ArithmeticFunction.sigma 2 n`, `τ(n)` is `n.divisors.card`, and the
harmonic mean of the squared divisors is `H₂(n) = τ(n) / ∑_{d ∣ n} 1/d²`,
written out in `ℚ`. The paper's factorizations `n = n₁ n₂ ⋯ n_m` into pairwise
coprime factors `n₁ < ⋯ < n_m` (Lemma 3(ii), Propositions 11 and 12) are read,
as in the paper's Remark 2, as the prime-power components of `n`; then `n₁` is
the least unitary divisor of `n` exceeding `1`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.SZumkeller
public import MathlibExt.NumberTheory.SumSquaredDivisorsProduct

namespace MetaMathlibExt

@[expose] public section

/-- **Number of unitary divisors.** A positive integer $n$ with $m$ distinct prime factors has
exactly $2^m$ unitary divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 2 (quoting Bege). -/
public theorem_wanted card_unitaryDivisors (n : ℕ) (hn : n ≠ 0) :
    (Nat.unitaryDivisors n).card = 2 ^ n.primeFactors.card

/-- **Sum of squares of unitary divisors.** For every positive integer $n$, the sum of the
squares of the unitary divisors of $n$ equals $\prod_{p} \left(1 + p^{2k_p}\right)$, where $p$
ranges over the distinct prime factors of $n$ and $k_p$ is the exponent of $p$ in $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 3(i) (quoting Subbarao and
Warren). -/
public theorem_wanted sum_sq_unitaryDivisors (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ Nat.unitaryDivisors n, d ^ 2 =
      ∏ p ∈ n.primeFactors, (1 + p ^ (2 * n.factorization p))

/-- **Properties of even s-Zumkeller numbers.** Let $n$ be an even s-Zumkeller number and let
$\sigma_2(n)$ be the sum of the squares of the positive divisors of $n$. Then $\sigma_2(n)$ is
even, some odd prime $p$ divides $n$ with an odd exponent in the prime factorization of $n$, and
$3n^2 \le 2\sigma_2(n)$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 1. -/
public theorem_wanted isSZumkeller_even_props (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    Even (ArithmeticFunction.sigma 2 n) ∧
      (∃ p ∈ n.primeFactors, Odd p ∧ Odd (n.factorization p)) ∧
      3 * n ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n

/-- **Even s-Zumkeller numbers have at least twelve divisors.** If $n$ is an even s-Zumkeller
number, then $n$ has at least $12$ positive divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 3. -/
public theorem_wanted twelve_le_card_divisors_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n)
    (he : Even n) : 12 ≤ n.divisors.card

/-- **Even s-Zumkeller numbers are divisible by 6.** Every even s-Zumkeller number is divisible
by $6$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Corollary 1. -/
public theorem_wanted six_dvd_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    6 ∣ n

/-- **A prime-factor product bound for s-Zumkeller numbers.** Let $n$ be an s-Zumkeller number
and let $p_1$ be its least prime factor. Then
$$\frac{2}{p_1^2} + 1 < \prod_{p} \frac{p^2}{p^2 - 1},$$
where the product ranges over the distinct prime factors $p$ of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 5. -/
public theorem_wanted two_div_minFac_sq_add_one_lt_prod (n : ℕ) (h : IsSZumkeller n) :
    2 / (n.minFac : ℚ) ^ 2 + 1 < ∏ p ∈ n.primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1)

/-- **Even s-Zumkeller numbers have at least three prime factors.** If $n$ is an even
s-Zumkeller number, then $n$ has at least $3$ distinct prime factors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 6(i). -/
public theorem_wanted three_le_card_primeFactors_of_isSZumkeller_even (n : ℕ)
    (h : IsSZumkeller n) (he : Even n) : 3 ≤ n.primeFactors.card

/-- **Odd s-Zumkeller numbers divisible by $3$ have at least eight prime factors.** Every odd
s-Zumkeller number divisible by $3$ has at least $8$ distinct prime factors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 6(ii). -/
public theorem_wanted eight_le_card_primeFactors_of_isSZumkeller_odd (n : ℕ)
    (h : IsSZumkeller n) (ho : Odd n) (h3 : 3 ∣ n) : 8 ≤ n.primeFactors.card

/-- **Odd s-Zumkeller numbers are perfect squares.** Every odd s-Zumkeller number is a perfect
square.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 7. -/
public theorem_wanted isSquare_of_isSZumkeller_odd (n : ℕ) (h : IsSZumkeller n) (ho : Odd n) :
    IsSquare n

/-- **Lower bound for odd s-Zumkeller numbers divisible by 3.** Every odd s-Zumkeller number $n$
divisible by $3$ satisfies
$n \ge 12442607161209225 = (3 \cdot 5 \cdot 7 \cdot 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23)^2$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 8. -/
public theorem_wanted le_of_isSZumkeller_odd_three_dvd (n : ℕ) (h : IsSZumkeller n)
    (ho : Odd n) (h3 : 3 ∣ n) : 12442607161209225 ≤ n

/-- **Harmonic mean of squared divisors of even s-Zumkeller numbers.** Let $n$ be an even
s-Zumkeller number and let $\tau(n)$ be the number of positive divisors of $n$. Then
$\tau(n) / \sum_{d \mid n} d^{-2} \le 2\tau(n)/3$, where the sum runs over the positive divisors
$d$ of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 9. -/
public theorem_wanted harmonicMeanSq_le_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n)
    (he : Even n) :
    (n.divisors.card : ℚ) / ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 ≤ 2 * n.divisors.card / 3

/-- **Lower bounds for unitary s-Zumkeller numbers.** Let $n$ be a unitary s-Zumkeller
number, let $q$ be the least unitary divisor of $n$ greater than $1$, and for each prime $p$
dividing $n$ let $k_p$ be the exponent of $p$ in $n$. Then, with both sums over all unitary
divisors $d$ of $n$ (including $n$ itself), $n^2 (2/q^2 + 1) \le \sum_d d^2$ and
$2/q^2 + 1 \le \sum_d 1/d^2$. Moreover $2/q^2 + 1 \le \prod_{p \mid n} (1 + p^{2k_p})/p^{2k_p}$,
the product running over the primes $p$ dividing $n$.

The number $q$ is the smallest of the prime powers $p^{k_p}$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 11. -/
public theorem_wanted isUnitarySZumkeller_bounds (n q : ℕ) (h : IsUnitarySZumkeller n)
    (hq : IsLeast {d | d ∈ Nat.unitaryDivisors n ∧ 1 < d} q) :
    (n : ℚ) ^ 2 * (2 / (q : ℚ) ^ 2 + 1) ≤ ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 ∧
      2 / (q : ℚ) ^ 2 + 1 ≤ ∑ d ∈ Nat.unitaryDivisors n, 1 / (d : ℚ) ^ 2 ∧
      2 / (q : ℚ) ^ 2 + 1 ≤
        ∏ p ∈ n.primeFactors,
          (1 + ((p : ℚ) ^ n.factorization p) ^ 2) / ((p : ℚ) ^ n.factorization p) ^ 2

/-- **Unitary divisor counts of unitary s-Zumkeller numbers.** Let $n$ be a unitary s-Zumkeller
number and let $q$ be the least unitary divisor of $n$ greater than $1$. If $q = 2$, then $n$ has
more than $2^6$ unitary divisors; if $q = 3$ or $q = 4$, then $n$ has more than $2^2$ unitary
divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 12. -/
public theorem_wanted card_unitaryDivisors_of_isUnitarySZumkeller (n q : ℕ)
    (h : IsUnitarySZumkeller n) (hq : IsLeast {d | d ∈ Nat.unitaryDivisors n ∧ 1 < d} q) :
    (q = 2 → 2 ^ 6 < (Nat.unitaryDivisors n).card) ∧
      (q = 3 → 2 ^ 2 < (Nat.unitaryDivisors n).card) ∧
      (q = 4 → 2 ^ 2 < (Nat.unitaryDivisors n).card)

/-- There is no odd unitary s-Zumkeller number.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 13. -/
public theorem_wanted not_isUnitarySZumkeller_of_odd (n : ℕ) (ho : Odd n) :
    ¬ IsUnitarySZumkeller n

end

end MetaMathlibExt

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
public import MathlibExt.NumberTheory.UnitaryDivisor

namespace MetaMathlibExt

@[expose] public section

/-- **s-Zumkeller numbers.** A natural number $n$ is s-Zumkeller if its proper divisors can be
split into two disjoint nonempty sets whose elements have equal sums of squares. Each of the two
sums is then $(\sigma_2(n) - n^2)/2$, where $\sigma_2(n)$ is the sum of the squares of the
positive divisors of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Definition 1. -/
def IsSZumkeller (n : ℕ) : Prop :=
  ∃ A ⊆ n.properDivisors, A.Nonempty ∧ (n.properDivisors \ A).Nonempty ∧
    ∑ d ∈ A, d ^ 2 = ∑ d ∈ n.properDivisors \ A, d ^ 2

/-- **Unitary s-Zumkeller numbers.** A natural number $n$ is a unitary s-Zumkeller number when
its proper unitary divisors (the unitary divisors of $n$ other than $n$) split into two nonempty
disjoint sets $A$ and $B$ with equal sums of squares, $\sum_{d \in A} d^2 = \sum_{d \in B} d^2$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Definition 2. -/
def IsUnitarySZumkeller (n : ℕ) : Prop :=
  ∃ A ⊆ (Nat.unitaryDivisors n).erase n, A.Nonempty ∧
    ((Nat.unitaryDivisors n).erase n \ A).Nonempty ∧
    ∑ d ∈ A, d ^ 2 = ∑ d ∈ (Nat.unitaryDivisors n).erase n \ A, d ^ 2

/-- **$60$ is s-Zumkeller.** The number $60$ is s-Zumkeller: the squares of its proper divisors
$1, 2, 5, 30$ sum to $1^2 + 2^2 + 5^2 + 30^2 = 930$, which is half of the sum of the squares of
all proper divisors of $60$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Example 1. -/
theorem isSZumkeller_sixty : IsSZumkeller 60 :=
  ⟨{1, 2, 5, 30}, by decide, by decide, by decide, by decide⟩

/-- **The number 6 is not s-Zumkeller.** The number $6$ is not an s-Zumkeller number: the squares of
its proper divisors sum to $1^2 + 2^2 + 3^2 = 14$, and they admit no split into two parts with
equal sums.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Section 1. -/
theorem not_isSZumkeller_six : ¬ IsSZumkeller 6 := by
  unfold IsSZumkeller; decide

/-- **The number 60 is unitary s-Zumkeller.** The number $60$ is a unitary s-Zumkeller number: its
proper unitary divisors are $1, 3, 4, 5, 12, 15, 20$, and $20^2 + 3^2 + 1^2 = 410$ is half the sum
of their squares.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Example 2. -/
theorem isUnitarySZumkeller_sixty : IsUnitarySZumkeller 60 :=
  ⟨{1, 3, 20}, by decide, by decide, by decide, by decide⟩

/-- **The number 6 is not unitary s-Zumkeller.** The number $6$ is not a unitary s-Zumkeller
number.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Section 1. -/
theorem not_isUnitarySZumkeller_six : ¬ IsUnitarySZumkeller 6 := by
  unfold IsUnitarySZumkeller; decide

/-- **Product formulas for the sum of divisors.** Let $n \ne 0$ be a natural number, let
$\sigma(n)$ be the sum of the divisors of $n$, and for each prime $p$ dividing $n$ let $k_p$ be
the exponent of $p$ in $n$. Then, with products over the primes $p$ dividing $n$,
$$\sigma(n) = \prod_{p \mid n} \frac{p^{k_p + 1} - 1}{p - 1}$$
and
$$\frac{\sigma(n)}{n} = \prod_{p \mid n} \frac{p^{k_p + 1} - 1}{p^{k_p} (p - 1)}.$$
If moreover $n > 1$, then $\sigma(n)/n < \prod_{p \mid n} p/(p - 1)$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 1(i) (quoting Peng and
Bhaskara Rao). -/
public theorem_wanted sigma_one_prod_formulas (n : ℕ) (hn : n ≠ 0) :
    (ArithmeticFunction.sigma 1 n : ℚ) =
        ∏ p ∈ n.primeFactors, ((p : ℚ) ^ (n.factorization p + 1) - 1) / (p - 1) ∧
      (ArithmeticFunction.sigma 1 n : ℚ) / n =
        ∏ p ∈ n.primeFactors,
          ((p : ℚ) ^ (n.factorization p + 1) - 1) / ((p : ℚ) ^ n.factorization p * (p - 1)) ∧
      (1 < n → (ArithmeticFunction.sigma 1 n : ℚ) / n < ∏ p ∈ n.primeFactors, (p : ℚ) / (p - 1))

/-- **Product formulas for the sum of squared divisors.** Let $n \ne 0$ be a natural number,
let $\sigma_2(n)$ be the sum of the squares of the divisors of $n$, and for each prime $p$
dividing $n$ let $k_p$ be the exponent of $p$ in $n$. Then, with products over the primes $p$
dividing $n$,
$$\sigma_2(n) = \prod_{p \mid n} \frac{p^{2(k_p + 1)} - 1}{p^2 - 1}$$
and
$$\frac{\sigma_2(n)}{n^2} = \prod_{p \mid n} \frac{p^{2(k_p + 1)} - 1}{p^{2k_p} (p^2 - 1)}.$$
If moreover $n > 1$, then $\sigma_2(n)/n^2 < \prod_{p \mid n} p^2/(p^2 - 1)$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 1(ii) (quoting Peng and
Bhaskara Rao). -/
public theorem_wanted sigma_two_prod_formulas (n : ℕ) (hn : n ≠ 0) :
    (ArithmeticFunction.sigma 2 n : ℚ) =
        ∏ p ∈ n.primeFactors, ((p : ℚ) ^ (2 * (n.factorization p + 1)) - 1) / (p ^ 2 - 1) ∧
      (ArithmeticFunction.sigma 2 n : ℚ) / n ^ 2 =
        ∏ p ∈ n.primeFactors,
          ((p : ℚ) ^ (2 * (n.factorization p + 1)) - 1) /
            ((p : ℚ) ^ (2 * n.factorization p) * (p ^ 2 - 1)) ∧
      (1 < n → (ArithmeticFunction.sigma 2 n : ℚ) / n ^ 2 <
        ∏ p ∈ n.primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1))

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

/-- **Criterion for even s-Zumkeller numbers.** Let $n$ be an even positive integer and let
$\sigma_2(n)$ be the sum of the squares of the positive divisors of $n$. Then $n$ is s-Zumkeller
if and only if there is a (possibly empty) set $S$ of proper divisors of $n$, not containing
$n/2$, such that $4 \sum_{d \in S} d^2 = 2\sigma_2(n) - 3n^2$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 2. -/
public theorem_wanted isSZumkeller_iff_of_even (n : ℕ) (hn : 0 < n) (he : Even n) :
    IsSZumkeller n ↔
      ∃ S ⊆ n.properDivisors.erase (n / 2),
        4 * (∑ d ∈ S, d ^ 2 : ℤ) = 2 * ArithmeticFunction.sigma 2 n - 3 * n ^ 2

/-- **Even s-Zumkeller numbers have at least twelve divisors.** If $n$ is an even s-Zumkeller
number, then $n$ has at least $12$ positive divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 3. -/
public theorem_wanted twelve_le_card_divisors_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n)
    (he : Even n) : 12 ≤ n.divisors.card

/-- **Even s-Zumkeller numbers are divisible by 3.** If $n$ is an even s-Zumkeller number, then
$3$ divides $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 4. -/
public theorem_wanted three_dvd_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    3 ∣ n

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

/-- **Harmonic mean of squared divisors of s-Zumkeller numbers $2^\alpha(2^{\alpha+1}-1)$.** Let
$\alpha \ge 1$ be an integer, let $n = 2^\alpha (2^{\alpha+1} - 1)$ and let $\tau(n)$ be the
number of positive divisors of $n$. If $n$ is s-Zumkeller, then
$\tau(n) / \sum_{d \mid n} d^{-2} < 2^{2\alpha+3}/3$, where the sum runs over the positive
divisors $d$ of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 10. -/
public theorem_wanted harmonicMeanSq_lt_of_isSZumkeller_mersenne (α n : ℕ) (hα : 1 ≤ α)
    (hn : n = 2 ^ α * (2 ^ (α + 1) - 1)) (h : IsSZumkeller n) :
    (n.divisors.card : ℚ) / ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 < 2 ^ (2 * α + 3) / 3

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

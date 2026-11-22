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

/-- `n` is an s-Zumkeller number: its proper divisors split into two nonempty
parts with equal sums of squares (each then equal to `(σ₂(n) - n²)/2`).

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Definition 1. -/
def IsSZumkeller (n : ℕ) : Prop :=
  ∃ A ⊆ n.properDivisors, A.Nonempty ∧ (n.properDivisors \ A).Nonempty ∧
    ∑ d ∈ A, d ^ 2 = ∑ d ∈ n.properDivisors \ A, d ^ 2

/-- `n` is a unitary s-Zumkeller number: its proper unitary divisors split into
two nonempty parts with equal sums of squares.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Definition 2. -/
def IsUnitarySZumkeller (n : ℕ) : Prop :=
  ∃ A ⊆ (Nat.unitaryDivisors n).erase n, A.Nonempty ∧
    ((Nat.unitaryDivisors n).erase n \ A).Nonempty ∧
    ∑ d ∈ A, d ^ 2 = ∑ d ∈ (Nat.unitaryDivisors n).erase n \ A, d ^ 2

/-- `60` is s-Zumkeller: `30² + 5² + 2² + 1² = 930` is half of the sum of the
squares of its proper divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Example 1. -/
theorem isSZumkeller_sixty : IsSZumkeller 60 :=
  ⟨{1, 2, 5, 30}, by decide, by decide, by decide, by decide⟩

/-- `6` is not s-Zumkeller (`1² + 2² + 3² = 14` admits no equal split).

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Section 1. -/
theorem not_isSZumkeller_six : ¬ IsSZumkeller 6 := by
  unfold IsSZumkeller; decide

/-- `60` is unitary s-Zumkeller: `20² + 3² + 1² = 410` is half of the sum of the
squares of its proper unitary divisors `1, 3, 4, 5, 12, 15, 20`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Example 2. -/
theorem isUnitarySZumkeller_sixty : IsUnitarySZumkeller 60 :=
  ⟨{1, 3, 20}, by decide, by decide, by decide, by decide⟩

/-- `6` is not unitary s-Zumkeller.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Section 1. -/
theorem not_isUnitarySZumkeller_six : ¬ IsUnitarySZumkeller 6 := by
  unfold IsUnitarySZumkeller; decide

/-- Product formulas for `σ(n)` and `σ(n)/n`, and `σ(n)/n < ∏ p/(p-1)` for
`n > 1`.

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

/-- Product formulas for `σ₂(n)` and `σ₂(n)/n²`, and `σ₂(n)/n² < ∏ p²/(p²-1)`
for `n > 1`.

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

/-- A positive integer with `m` distinct prime factors has `2^m` unitary
divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 2 (quoting Bege). -/
public theorem_wanted card_unitaryDivisors (n : ℕ) (hn : n ≠ 0) :
    (Nat.unitaryDivisors n).card = 2 ^ n.primeFactors.card

/-- `σ₂*(n) = ∏ (1 + p^{2k})` over the prime powers `p^k ∥ n`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Lemma 3(i) (quoting Subbarao and
Warren). -/
public theorem_wanted sum_sq_unitaryDivisors (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ Nat.unitaryDivisors n, d ^ 2 =
      ∏ p ∈ n.primeFactors, (1 + p ^ (2 * n.factorization p))

/-- An even s-Zumkeller number `n` has `σ₂(n)` even, some odd prime with odd
exponent, and `σ₂(n) ≥ 3n²/2`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 1. -/
public theorem_wanted isSZumkeller_even_props (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    Even (ArithmeticFunction.sigma 2 n) ∧
      (∃ p ∈ n.primeFactors, Odd p ∧ Odd (n.factorization p)) ∧
      3 * n ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n

/-- An even positive `n` is s-Zumkeller iff `(2σ₂(n) - 3n²)/4` is a (possibly
empty) sum of squares of distinct proper divisors of `n` other than `n/2`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 2. -/
public theorem_wanted isSZumkeller_iff_of_even (n : ℕ) (hn : 0 < n) (he : Even n) :
    IsSZumkeller n ↔
      ∃ S ⊆ n.properDivisors.erase (n / 2),
        4 * (∑ d ∈ S, d ^ 2 : ℤ) = 2 * ArithmeticFunction.sigma 2 n - 3 * n ^ 2

/-- An even s-Zumkeller number has at least `12` divisors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 3. -/
public theorem_wanted twelve_le_card_divisors_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n)
    (he : Even n) : 12 ≤ n.divisors.card

/-- An even s-Zumkeller number is divisible by `3`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 4. -/
public theorem_wanted three_dvd_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    3 ∣ n

/-- An even s-Zumkeller number is divisible by `6`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Corollary 1. -/
public theorem_wanted six_dvd_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n) (he : Even n) :
    6 ∣ n

/-- For an s-Zumkeller number with least prime factor `p₁`,
`2/p₁² + 1 < ∏_{p ∣ n} p²/(p² - 1)`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 5. -/
public theorem_wanted two_div_minFac_sq_add_one_lt_prod (n : ℕ) (h : IsSZumkeller n) :
    2 / (n.minFac : ℚ) ^ 2 + 1 < ∏ p ∈ n.primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1)

/-- An even s-Zumkeller number has at least `3` distinct prime factors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 6(i). -/
public theorem_wanted three_le_card_primeFactors_of_isSZumkeller_even (n : ℕ)
    (h : IsSZumkeller n) (he : Even n) : 3 ≤ n.primeFactors.card

/-- An odd s-Zumkeller number divisible by `3` has at least `8` distinct prime
factors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 6(ii). -/
public theorem_wanted eight_le_card_primeFactors_of_isSZumkeller_odd (n : ℕ)
    (h : IsSZumkeller n) (ho : Odd n) (h3 : 3 ∣ n) : 8 ≤ n.primeFactors.card

/-- An odd s-Zumkeller number is a perfect square.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 7. -/
public theorem_wanted isSquare_of_isSZumkeller_odd (n : ℕ) (h : IsSZumkeller n) (ho : Odd n) :
    IsSquare n

/-- An odd s-Zumkeller number divisible by `3` is at least
`12442607161209225 = (3·5·7·11·13·17·19·23)²`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 8. -/
public theorem_wanted le_of_isSZumkeller_odd_three_dvd (n : ℕ) (h : IsSZumkeller n)
    (ho : Odd n) (h3 : 3 ∣ n) : 12442607161209225 ≤ n

/-- For an even s-Zumkeller number, `H₂(n) = τ(n) / ∑_{d ∣ n} 1/d² ≤ 2τ(n)/3`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 9. -/
public theorem_wanted harmonicMeanSq_le_of_isSZumkeller (n : ℕ) (h : IsSZumkeller n)
    (he : Even n) :
    (n.divisors.card : ℚ) / ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 ≤ 2 * n.divisors.card / 3

/-- If `n = 2^α (2^{α+1} - 1)` with `α ≥ 1` is s-Zumkeller, then
`H₂(n) < 2^{2α+3}/3`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 10. -/
public theorem_wanted harmonicMeanSq_lt_of_isSZumkeller_mersenne (α n : ℕ) (hα : 1 ≤ α)
    (hn : n = 2 ^ α * (2 ^ (α + 1) - 1)) (h : IsSZumkeller n) :
    (n.divisors.card : ℚ) / ∑ d ∈ n.divisors, 1 / (d : ℚ) ^ 2 < 2 ^ (2 * α + 3) / 3

/-- For a unitary s-Zumkeller number `n` whose least unitary divisor exceeding
`1` is `q` (the smallest prime-power component of `n`):
`σ₂*(n) ≥ n²(2/q² + 1)`, hence `2/q² + 1 ≤ ∑_{d unitary} 1/d²` and
`2/q² + 1 ≤ ∏_{p^k ∥ n} (1 + p^{2k})/p^{2k}`.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 11. -/
public theorem_wanted isUnitarySZumkeller_bounds (n q : ℕ) (h : IsUnitarySZumkeller n)
    (hq : IsLeast {d | d ∈ Nat.unitaryDivisors n ∧ 1 < d} q) :
    (n : ℚ) ^ 2 * (2 / (q : ℚ) ^ 2 + 1) ≤ ∑ d ∈ Nat.unitaryDivisors n, (d : ℚ) ^ 2 ∧
      2 / (q : ℚ) ^ 2 + 1 ≤ ∑ d ∈ Nat.unitaryDivisors n, 1 / (d : ℚ) ^ 2 ∧
      2 / (q : ℚ) ^ 2 + 1 ≤
        ∏ p ∈ n.primeFactors,
          (1 + ((p : ℚ) ^ n.factorization p) ^ 2) / ((p : ℚ) ^ n.factorization p) ^ 2

/-- For a unitary s-Zumkeller number whose least unitary divisor exceeding `1`
is `2`, `3` or `4`, the number of unitary divisors exceeds `2⁶`, `2²` or `2²`
respectively.

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

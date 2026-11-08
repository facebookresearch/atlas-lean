/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-near perfect numbers of the forms `2^k p` and `2^k p^2`

Statements from Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua
Zelinsky, *On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61 (arXiv:2310.01305).
Labels follow the journal numbering; the arXiv version numbers Lemmas 1-10 as Lemmas 3-7,
10, 11, 14, 15, 17 and Propositions 1-5 as Propositions 8, 9, 12, 13, 16.

A number `n` is `2`-near perfect with omitted divisors `d₁ ≠ d₂` when `d₁, d₂ ∣ n` and
`σ(n) = 2n + d₁ + d₂`. It is strongly `2`-near perfect when it has a divisor `d` with
`σ(n) = 2n + d + n / d` (the paper's equivalent form of the definition); for `n = 2^k p`
with `p` odd, `d ≠ n / d` holds automatically. Exponents flattened in the extracted
statements (`2k+1`, `pk`) are read as powers, as in the paper.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 1: if `n = 2^k p` (`p` prime, `k > 0`) is `2`-near perfect with omitted divisors
`d₁, d₂`, then up to swapping `d₁, d₂` one of: (1) `p = 2^k - 1`, `d₁ = 1`, `d₂ = p`;
(2) `p = 2^(k+1) - 2^a - 2^b - 1`, `d₁ = 2^a`, `d₂ = 2^b`; (3)
`p = (2^(k+1) - 2^a - 1) / (1 + 2^b)`, `d₁ = 2^a`, `d₂ = 2^b p`; (4)
`p = (2^(k+1) - 1) / (1 + 2^a + 2^b)`, `d₁ = 2^a p`, `d₂ = 2^b p`, for some `a, b ∈ ℕ`.
Quotients are written as products. The paper states only this necessary direction; the four
situations are not sufficient as printed (`k = 3`, `a = b = 1` gives the prime `p = 11` in
situation 2, but `d₁ = d₂ = 2`).

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Theorem 1
(`integers-2024-A61-thm-1`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_cases {k p d₁ d₂ : ℕ} (hk : 0 < k)
    (hp : p.Prime) (hd₁ : d₁ ∣ 2 ^ k * p) (hd₂ : d₂ ∣ 2 ^ k * p) (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p) = 2 * (2 ^ k * p) + d₁ + d₂) :
    ∃ e₁ e₂ : ℕ, ((e₁ = d₁ ∧ e₂ = d₂) ∨ (e₁ = d₂ ∧ e₂ = d₁)) ∧
      (((p : ℤ) = 2 ^ k - 1 ∧ e₁ = 1 ∧ e₂ = p) ∨
        (∃ a b : ℕ, (p : ℤ) = 2 ^ (k + 1) - 2 ^ a - 2 ^ b - 1 ∧ e₁ = 2 ^ a ∧ e₂ = 2 ^ b) ∨
        (∃ a b : ℕ, (p : ℤ) * (1 + 2 ^ b) = 2 ^ (k + 1) - 2 ^ a - 1 ∧
          e₁ = 2 ^ a ∧ e₂ = 2 ^ b * p) ∨
        (∃ a b : ℕ, (p : ℤ) * (1 + 2 ^ a + 2 ^ b) = 2 ^ (k + 1) - 1 ∧
          e₁ = 2 ^ a * p ∧ e₂ = 2 ^ b * p))

/-- Theorem 2: if `n = 2^k p^2` (`p` prime) is `2`-near perfect, then `n ∈ {18, 36, 200}`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Theorem 2
(`integers-2024-A61-thm-2`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_sq {k p d₁ d₂ : ℕ} (hp : p.Prime)
    (hd₁ : d₁ ∣ 2 ^ k * p ^ 2) (hd₂ : d₂ ∣ 2 ^ k * p ^ 2) (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + d₁ + d₂) :
    2 ^ k * p ^ 2 = 18 ∨ 2 ^ k * p ^ 2 = 36 ∨ 2 ^ k * p ^ 2 = 200

/-- Lemma 2: for integers `1 ≤ a ≤ k`, if `D = 2^(2k+2) + 2^(k+2) - 2^(a+2) - 7` is a
perfect square, then `k = a = 1`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 2
(`integers-2024-A61-lem-2`). -/
public theorem_wanted eq_one_of_isSquare_discriminant {a k : ℕ} (ha : 0 < a) (hak : a ≤ k)
    (hD : IsSquare ((2 : ℤ) ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7)) :
    k = 1 ∧ a = 1

/-- Lemma 3: if `b, k ≥ 0`, `p` is odd and
`(2^(k+1) - 1)(p^2 + p + 1) = 2^(k+1) p^2 + 2^b p + 1`, then `p ∣ 2^k - 1` and
`p + 1 ∣ 2^b - 2`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 3
(`integers-2024-A61-lem-3`). -/
public theorem_wanted dvd_of_two_near_perfect_eq_six {b k p : ℕ} (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p + 1) :
    (p : ℤ) ∣ 2 ^ k - 1 ∧ (p + 1 : ℤ) ∣ 2 ^ b - 2

/-- Lemma 4: `(2^(k+1) - 1)(p^2 + p + 1) = 2^(k+1) p^2 + 2^b p + 1` has no solution with
`p` odd and `2 ≤ b ≤ k - 1`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 4
(`integers-2024-A61-lem-4`). -/
public theorem_wanted not_two_near_perfect_eq_seven {b k p : ℕ} (hp : Odd p) (hb : 2 ≤ b)
    (hbk : b + 1 ≤ k) :
    ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) ≠ 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p + 1

/-- Lemma 5: if `n = 2^k p^2` (`p` an odd prime) is `2`-near perfect with omitted divisors
`d₁, d₂`, then `d₁ + d₂ = -p^2 + (2^(k+1) - 1) p + (2^(k+1) - 1)` and `d₁, d₂` have
opposite parity.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 5
(`integers-2024-A61-lem-5`). -/
public theorem_wanted omitted_divisors_sum_two_pow_mul_prime_sq {k p d₁ d₂ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd₁ : d₁ ∣ 2 ^ k * p ^ 2) (hd₂ : d₂ ∣ 2 ^ k * p ^ 2)
    (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + d₁ + d₂) :
    ((d₁ + d₂ : ℕ) : ℤ) = -(p : ℤ) ^ 2 + (2 ^ (k + 1) - 1) * p + (2 ^ (k + 1) - 1) ∧
      d₁ % 2 ≠ d₂ % 2

/-- Lemma 6: if `k, b > 0`, `p` is odd and
`(2^(k+1) - 1)(p^2 + p + 1) = 2^(k+1) p^2 + 2^b p^2 + 1` (Equation (12)), then
`p ∣ 2^k - 1`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 6
(`integers-2024-A61-lem-6`). -/
public theorem_wanted dvd_of_two_near_perfect_eq_twelve {b k p : ℕ} (hk : 0 < k) (hb : 0 < b)
    (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p ^ 2 + 1) :
    (p : ℤ) ∣ 2 ^ k - 1

/-- Lemma 7: an odd solution `p` of Equation (12) (with `k, b > 0`, as in Lemma 6)
satisfies `p + 1 ∣ 2^b + 2`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 7
(`integers-2024-A61-lem-7`). -/
public theorem_wanted succ_dvd_of_two_near_perfect_eq_twelve {b k p : ℕ} (hk : 0 < k)
    (hb : 0 < b) (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p ^ 2 + 1) :
    (p + 1 : ℤ) ∣ 2 ^ b + 2

/-- Lemma 8: if `n = 2^k p` (`p` an odd prime) is strongly `2`-near perfect, then
`p = (2^(k+1) - 2^a - 1) / (1 + 2^(k-a))` for some `a ≤ k`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 8
(`integers-2024-A61-lem-8`). -/
public theorem_wanted strong_two_near_perfect_two_pow_mul_prime_form {k p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hstrong : ∃ d, d ∣ 2 ^ k * p ∧
      ArithmeticFunction.sigma 1 (2 ^ k * p) = 2 * (2 ^ k * p) + d + 2 ^ k * p / d) :
    ∃ a ≤ k, (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1

/-- Lemma 9: if `n = 2^k p` with `p` prime and `p = (2^(k+1) - 2^a - 1) / (1 + 2^(k-a))`,
`a ≤ k`, then `k < 2a`. The paper also assumes `n` strongly `2`-near perfect; that follows
from the form of `p` (take `d = 2^a`), so the hypothesis is dropped.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 9
(`integers-2024-A61-lem-9`). -/
public theorem_wanted lt_two_mul_of_strong_two_near_perfect_form {a k p : ℕ} (hp : p.Prime)
    (hak : a ≤ k) (hform : (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1) :
    k < 2 * a

/-- Lemma 10: if `b ≥ 1` and `2^b + 1 ∣ 3 · 2^a + 1`, then `b = 2`. As printed the lemma
has no range for `b`; the proof divides `a` by `b` (`a = bq + r`, `0 ≤ r < b`), so
`b ≥ 1` is assumed. For `b = 0` it fails: `2 ∣ 3 · 2^0 + 1 = 4`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 10
(`integers-2024-A61-lem-10`). -/
public theorem_wanted eq_two_of_two_pow_add_one_dvd {a b : ℕ} (hb : 1 ≤ b)
    (h : 2 ^ b + 1 ∣ 3 * 2 ^ a + 1) : b = 2

/-- Proposition 1 (Case 1: both omitted divisors are powers of `2`): if `n = 2^k p^2`
(`p` an odd prime) is `2`-near perfect with omitted divisors `2^i ≠ 2^j`, `i, j ≤ k`, then
`n = 18` and the omitted divisors are `1` and `2`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 1
(`integers-2024-A61-prop-1`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_sq_case_one {k p i j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i ≤ k) (hj : j ≤ k) (hij : i ≠ j)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + 2 ^ i + 2 ^ j) :
    2 ^ k * p ^ 2 = 18 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))

/-- Proposition 2 (Case 2: omitted divisors `2^i`, `i ≤ k`, and `p^m`, `m ∈ {1, 2}`): no
`n = 2^k p^2` (`p` an odd prime) is `2`-near perfect with such omitted divisors.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 2
(`integers-2024-A61-prop-2`). -/
public theorem_wanted not_two_near_perfect_two_pow_mul_prime_sq_case_two {k p i m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i ≤ k) (hm : m = 1 ∨ m = 2) :
    ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) ≠ 2 * (2 ^ k * p ^ 2) + 2 ^ i + p ^ m

/-- Proposition 3 (Case 3 with omitted divisors `1` and `2^b p^2`, `1 ≤ b ≤ k`): if
`n = 2^k p^2` (`p` an odd prime) is `2`-near perfect with these omitted divisors, then
`n = 36` and the omitted divisors are `1` and `18`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 3
(`integers-2024-A61-prop-3`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_sq_case_three {k p b : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) =
      2 * (2 ^ k * p ^ 2) + 1 + 2 ^ b * p ^ 2) :
    2 ^ k * p ^ 2 = 36 ∧ 2 ^ b * p ^ 2 = 18

/-- Proposition 4 (Case V: omitted divisors `p^m`, `m ∈ {1, 2}`, and `2^b p^j`,
`1 ≤ b ≤ k`, `j ∈ {1, 2}`): if `n = 2^k p^2` (`p` an odd prime) is `2`-near perfect with
such omitted divisors, then `n = 200`.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 4
(`integers-2024-A61-prop-4`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_sq_case_five {k p m b j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : m = 1 ∨ m = 2) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hj : j = 1 ∨ j = 2)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) =
      2 * (2 ^ k * p ^ 2) + p ^ m + 2 ^ b * p ^ j) :
    2 ^ k * p ^ 2 = 200

/-- Proposition 5: if `n = 2^k p` with `p` prime and `p = (2^(k+1) - 2^a - 1) / (1 + 2^(k-a))`,
`a ≤ k`, then `k = a + 2`, the omitted divisors are `d₁ = 2^a` and `d₂ = n / d₁ = 4p`,
`p = (2^(a+3) - 2^a - 1) / 5`, and `a ≡ 3 (mod 4)`. The paper's hypothesis that `n` is
strongly `2`-near perfect follows from the form of `p` and is dropped.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 5
(`integers-2024-A61-prop-5`). -/
public theorem_wanted strong_two_near_perfect_two_pow_mul_prime_classification {a k p : ℕ}
    (hp : p.Prime) (hak : a ≤ k)
    (hform : (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1) :
    k = a + 2 ∧ 2 ^ k * p / 2 ^ a = 4 * p ∧ (5 * p : ℤ) = 2 ^ (a + 3) - 2 ^ a - 1 ∧
      a % 4 = 3

end

end MetaMathlibExt

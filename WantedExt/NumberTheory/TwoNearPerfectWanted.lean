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

/-- **$2$-near perfect numbers of the form $2^k p$.** Let $k \ge 1$, let $p$ be a prime and let
$n = 2^k p$. Suppose $d_1 \ne d_2$ are divisors of $n$ with $\sigma(n) = 2n + d_1 + d_2$, where
$\sigma$ is the sum-of-divisors function (that is, $n$ is $2$-near perfect with omitted divisors
$d_1, d_2$). Then, after possibly swapping $d_1$ and $d_2$, one of the following holds, where
all equations are between integers: (1) $p = 2^k - 1$, $d_1 = 1$ and $d_2 = p$; (2) for some
natural numbers $a, b$, $p = 2^{k+1} - 2^a - 2^b - 1$, $d_1 = 2^a$ and $d_2 = 2^b$; (3) for some
natural numbers $a, b$, $p(1 + 2^b) = 2^{k+1} - 2^a - 1$, $d_1 = 2^a$ and $d_2 = 2^b p$; (4) for
some natural numbers $a, b$, $p(1 + 2^a + 2^b) = 2^{k+1} - 1$, $d_1 = 2^a p$ and $d_2 = 2^b p$.

The paper states only this necessary direction; the four situations are not sufficient as
printed ($k = 3$, $a = b = 1$ gives the prime $p = 11$ in situation 2, but $d_1 = d_2 = 2$).

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

/-- **$2$-near perfect numbers of the form $2^k p^2$.** Let $p$ be a prime, let $k$ be a natural
number and let $n = 2^k p^2$. If $n$ has divisors $d_1 \ne d_2$ with
$\sigma(n) = 2n + d_1 + d_2$, where $\sigma$ is the sum-of-divisors function (that is, $n$ is
$2$-near perfect with omitted divisors $d_1, d_2$), then $n$ is $18$, $36$ or $200$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Theorem 2
(`integers-2024-A61-thm-2`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_sq {k p d₁ d₂ : ℕ} (hp : p.Prime)
    (hd₁ : d₁ ∣ 2 ^ k * p ^ 2) (hd₂ : d₂ ∣ 2 ^ k * p ^ 2) (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + d₁ + d₂) :
    2 ^ k * p ^ 2 = 18 ∨ 2 ^ k * p ^ 2 = 36 ∨ 2 ^ k * p ^ 2 = 200

/-- **Square values of the discriminant $2^{2k+2} + 2^{k+2} - 2^{a+2} - 7$.** Let $a$ and $k$ be
natural numbers with $1 \le a \le k$. If $2^{2k+2} + 2^{k+2} - 2^{a+2} - 7$ is the square of an
integer, then $k = a = 1$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 2
(`integers-2024-A61-lem-2`). -/
public theorem_wanted eq_one_of_isSquare_discriminant {a k : ℕ} (ha : 0 < a) (hak : a ≤ k)
    (hD : IsSquare ((2 : ℤ) ^ (2 * k + 2) + 2 ^ (k + 2) - 2 ^ (a + 2) - 7)) :
    k = 1 ∧ a = 1

/-- **Divisibility constraints on odd solutions of $(2^{k+1} - 1)(p^2 + p + 1) =
2^{k+1} p^2 + 2^b p + 1$.** Let $b$ and $k$ be natural numbers and let $p$ be an odd natural
number such that $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p + 1$. Then, as integers, $p$
divides $2^k - 1$ and $p + 1$ divides $2^b - 2$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 3
(`integers-2024-A61-lem-3`). -/
public theorem_wanted dvd_of_two_near_perfect_eq_six {b k p : ℕ} (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p + 1) :
    (p : ℤ) ∣ 2 ^ k - 1 ∧ (p + 1 : ℤ) ∣ 2 ^ b - 2

/-- **No odd solutions of $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p + 1$ for
$2 \le b \le k - 1$.** Let $b$ and $k$ be natural numbers with $2 \le b$ and $b + 1 \le k$, and
let $p$ be an odd natural number. Then $(2^{k+1} - 1)(p^2 + p + 1) \ne 2^{k+1} p^2 + 2^b p + 1$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 4
(`integers-2024-A61-lem-4`). -/
public theorem_wanted not_two_near_perfect_eq_seven {b k p : ℕ} (hp : Odd p) (hb : 2 ≤ b)
    (hbk : b + 1 ≤ k) :
    ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) ≠ 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p + 1

/-- **Sum and parity of the omitted divisors of a $2$-near perfect $2^k p^2$.** Let $p$ be an odd
prime, let $k$ be a natural number, and let $d_1 \ne d_2$ be divisors of $n = 2^k p^2$ with
$\sigma(n) = 2n + d_1 + d_2$, where $\sigma$ denotes the sum of divisors. Then
$d_1 + d_2 = -p^2 + (2^{k+1} - 1) p + (2^{k+1} - 1)$, and $d_1$ and $d_2$ have opposite parity.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 5
(`integers-2024-A61-lem-5`). -/
public theorem_wanted omitted_divisors_sum_two_pow_mul_prime_sq {k p d₁ d₂ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd₁ : d₁ ∣ 2 ^ k * p ^ 2) (hd₂ : d₂ ∣ 2 ^ k * p ^ 2)
    (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + d₁ + d₂) :
    ((d₁ + d₂ : ℕ) : ℤ) = -(p : ℤ) ^ 2 + (2 ^ (k + 1) - 1) * p + (2 ^ (k + 1) - 1) ∧
      d₁ % 2 ≠ d₂ % 2

/-- **Odd solutions $p$ of $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p^2 + 1$ divide
$2^k - 1$.** Let $k$ and $b$ be positive natural numbers and let $p$ be an odd natural number
such that $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p^2 + 1$. Then $p$ divides $2^k - 1$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 6
(`integers-2024-A61-lem-6`). -/
public theorem_wanted dvd_of_two_near_perfect_eq_twelve {b k p : ℕ} (hk : 0 < k) (hb : 0 < b)
    (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p ^ 2 + 1) :
    (p : ℤ) ∣ 2 ^ k - 1

/-- **Odd solutions $p$ of $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p^2 + 1$ satisfy
$p + 1 \mid 2^b + 2$.** Let $k$ and $b$ be positive natural numbers and let $p$ be an odd natural
number such that $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p^2 + 1$. Then, as integers,
$p + 1$ divides $2^b + 2$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 7
(`integers-2024-A61-lem-7`). -/
public theorem_wanted succ_dvd_of_two_near_perfect_eq_twelve {b k p : ℕ} (hk : 0 < k)
    (hb : 0 < b) (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p ^ 2 + 1) :
    (p + 1 : ℤ) ∣ 2 ^ b + 2

/-- **Strongly $2$-near perfect numbers of the form $2^k p$.** Let $p$ be an odd prime, let $k$
be a natural number and let $n = 2^k p$. Suppose that $n$ is strongly $2$-near perfect, that is,
$\sigma(n) = 2n + d + n/d$ for some divisor $d$ of $n$, where $\sigma$ is the sum-of-divisors
function. Then there is a natural number $a \le k$ with $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$,
that is, $p = (2^{k+1} - 2^a - 1)/(1 + 2^{k-a})$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 8
(`integers-2024-A61-lem-8`). -/
public theorem_wanted strong_two_near_perfect_two_pow_mul_prime_form {k p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hstrong : ∃ d, d ∣ 2 ^ k * p ∧
      ArithmeticFunction.sigma 1 (2 ^ k * p) = 2 * (2 ^ k * p) + d + 2 ^ k * p / d) :
    ∃ a ≤ k, (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1

/-- **Prime solutions of $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$ satisfy $k < 2a$.** Let $a \le k$
be natural numbers and let $p$ be a prime with $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$, that is,
$p = (2^{k+1} - 2^a - 1)/(1 + 2^{k-a})$. Then $k < 2a$.

The source also assumes that $n = 2^k p$ is strongly $2$-near perfect, that is, that
$\sigma(n) = 2n + d + n/d$ for some divisor $d$ of $n$, where $\sigma$ is the sum of divisors.
This follows from the equation for $p$ by taking $d = 2^a$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 9
(`integers-2024-A61-lem-9`). -/
public theorem_wanted lt_two_mul_of_strong_two_near_perfect_form {a k p : ℕ} (hp : p.Prime)
    (hak : a ≤ k) (hform : (p : ℤ) * (1 + 2 ^ (k - a)) = 2 ^ (k + 1) - 2 ^ a - 1) :
    k < 2 * a

/-- **If $b \ge 1$ and $2^b + 1$ divides $3 \cdot 2^a + 1$, then $b = 2$.** Let $a$ and $b$ be
natural numbers with $b \ge 1$. If $2^b + 1$ divides $3 \cdot 2^a + 1$, then $b = 2$.

The source prints the lemma with no range for $b$; its proof divides $a$ by $b$, so $b \ge 1$ is
assumed here. The hypothesis is needed: for $b = 0$, $2^0 + 1 = 2$ divides $3 \cdot 2^0 + 1 = 4$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 10
(`integers-2024-A61-lem-10`). -/
public theorem_wanted eq_two_of_two_pow_add_one_dvd {a b : ℕ} (hb : 1 ≤ b)
    (h : 2 ^ b + 1 ∣ 3 * 2 ^ a + 1) : b = 2

/-- **$2$-near perfect $2^k p^2$ whose omitted divisors are powers of $2$.** Let $p$ be an odd
prime, let $k$ be a natural number and let $i \ne j$ be natural numbers with $i \le k$ and
$j \le k$. If $n = 2^k p^2$ satisfies $\sigma(n) = 2n + 2^i + 2^j$, where $\sigma$ is the
sum-of-divisors function (that is, $n$ is $2$-near perfect with omitted divisors $2^i$ and
$2^j$), then $n = 18$ and either $i = 0, j = 1$ or $i = 1, j = 0$, so the omitted divisors are
$1$ and $2$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 1
(`integers-2024-A61-prop-1`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_sq_case_one {k p i j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i ≤ k) (hj : j ≤ k) (hij : i ≠ j)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + 2 ^ i + 2 ^ j) :
    2 ^ k * p ^ 2 = 18 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))

/-- **No $2$-near perfect $2^k p^2$ with omitted divisors $2^i$ and $p$ or $p^2$.** Let $p$ be an
odd prime, let $k$ and $i$ be natural numbers with $i \le k$, let $m$ be $1$ or $2$, and let
$n = 2^k p^2$. Then $\sigma(n) \ne 2n + 2^i + p^m$, where $\sigma$ is the sum-of-divisors
function; that is, $n$ is not $2$-near perfect with omitted divisors $2^i$ and $p^m$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 2
(`integers-2024-A61-prop-2`). -/
public theorem_wanted not_two_near_perfect_two_pow_mul_prime_sq_case_two {k p i m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i ≤ k) (hm : m = 1 ∨ m = 2) :
    ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) ≠ 2 * (2 ^ k * p ^ 2) + 2 ^ i + p ^ m

/-- **$2$-near perfect $2^k p^2$ with omitted divisors $1$ and $2^b p^2$.** Let $p$ be an odd
prime and let $b, k$ be integers with $1 \le b \le k$. If $n = 2^k p^2$ satisfies
$\sigma(n) = 2n + 1 + 2^b p^2$, where $\sigma$ is the sum-of-divisors function (that is, $n$ is
$2$-near perfect with omitted divisors $1$ and $2^b p^2$), then $n = 36$ and $2^b p^2 = 18$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 3
(`integers-2024-A61-prop-3`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_sq_case_three {k p b : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) =
      2 * (2 ^ k * p ^ 2) + 1 + 2 ^ b * p ^ 2) :
    2 ^ k * p ^ 2 = 36 ∧ 2 ^ b * p ^ 2 = 18

/-- **$2$-near perfect $2^k p^2$ with omitted divisors $p^m$ and $2^b p^j$.** Let $p$ be an odd
prime, let each of $m$ and $j$ be $1$ or $2$, and let $b, k$ be integers with $1 \le b \le k$.
If $n = 2^k p^2$ satisfies $\sigma(n) = 2n + p^m + 2^b p^j$, where $\sigma$ is the
sum-of-divisors function (that is, $n$ is $2$-near perfect with omitted divisors $p^m$ and
$2^b p^j$), then $n = 200$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 4
(`integers-2024-A61-prop-4`). -/
public theorem_wanted two_near_perfect_two_pow_mul_prime_sq_case_five {k p m b j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : m = 1 ∨ m = 2) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hj : j = 1 ∨ j = 2)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) =
      2 * (2 ^ k * p ^ 2) + p ^ m + 2 ^ b * p ^ j) :
    2 ^ k * p ^ 2 = 200

/-- **Classification of prime solutions of $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$.** Let $a \le k$
be natural numbers and let $p$ be a prime with $p(1 + 2^{k-a}) = 2^{k+1} - 2^a - 1$, that is,
$p = (2^{k+1} - 2^a - 1)/(1 + 2^{k-a})$. Then $k = a + 2$, $2^k p / 2^a = 4p$,
$5p = 2^{a+3} - 2^a - 1$, and $a \equiv 3 \pmod 4$.

The source states this for $n = 2^k p$ strongly $2$-near perfect, that is, with
$\sigma(n) = 2n + d + n/d$ for some divisor $d$ of $n$, where $\sigma$ is the sum of divisors.
That hypothesis follows from the equation for $p$ by taking $d = 2^a$.

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

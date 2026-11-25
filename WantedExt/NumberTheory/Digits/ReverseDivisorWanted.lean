/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Which integer divides the reverse of any of its multiples?

Statements from Mohamed Ayad and Rachid Bouchenna,
"Which Integer Divides the Reverse of Any of Its
Multiples?", *INTEGERS* 25 (2025), Article A37
(<https://math.colgate.edu/~integers/vol25.html>).

Digit reversal is MathlibExt's
`Nat.reverseDigits b n`. A *reverse divisor* is a
positive integer `n` whose decimal reversal is a
multiple `k * n` with `k ≥ 2` (the *quotient*); `n` has
the *property `P*`* if it divides the reversal of each
of its multiples. The main theorem (Theorem 3) says
`P*` holds exactly for the divisors of `99`. All
claims below were checked numerically (all reverse
divisors below `2 * 10^6`, and `P*` for the divisors
of `99` against all multiples below `3 * 10^5`).

Lemma 3 uses the paper's Notation 1: `S_r = 10 9^r 89`
(the basic quotient-9 reverse divisor `11 (10^{r+2} - 1)`).
Not stated (see the source audit table): Theorem 2 (the
block structure of non-basic quotient-9 reverse
divisors), whose printed form is not symmetric and
admits non-reverse-divisors such as `1089 0 1089 1089`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.Digits.BasicReverseDivisors
public import MathlibExt.NumberTheory.Digits.ReverseDivisibility
public import MathlibExt.NumberTheory.Digits.ReverseDivisor
public import MathlibExt.NumberTheory.Digits.ReverseDivisorCoprime
public import MathlibExt.NumberTheory.Digits.ReverseDivisorFourDigits
public import MathlibExt.NumberTheory.Digits.ReverseDivisorQuotientFour

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- **The positive integers with property $P^*$ are the divisors of $99$.** A natural number
$n \ge 1$ has property $P^*$ if and only if $n$ divides $99$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 3. -/
theorem_wanted hasPropertyPStar_iff_dvd (n : ℕ) (hn : 1 ≤ n) :
    HasPropertyPStar n ↔ n ∣ 99

/-- **Divisors of $99$ have property $P^*$.** Every divisor of $99$ has property $P^*$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 1. -/
theorem_wanted hasPropertyPStar_of_dvd (n : ℕ) (hn : n ∣ 99) :
    HasPropertyPStar n

/-- **Palindromes with property $P^*$.** Let $n \ge 1$ be a natural number that is a decimal
palindrome, that is, whose decimal reversal equals $n$. If $n$ has the property $P^*$, then $n$
is one of $1$, $3$, $9$, $11$, $33$ and $99$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 3. -/
theorem_wanted palindrome_hasPropertyPStar (n : ℕ) (hn : 1 ≤ n)
    (hpal : Nat.reverseDigits 10 n = n) (h : HasPropertyPStar n) :
    n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 11 ∨ n = 33 ∨ n = 99

/-- **Reverse divisors have quotient $4$ or $9$.** If $n$ is a reverse divisor, then the decimal
reversal of $n$ equals $4n$ or $9n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem_wanted reverseDigits_eq_four_or_nine_mul (n : ℕ)
    (h : IsReverseDivisor n) :
    Nat.reverseDigits 10 n = 4 * n ∨ Nat.reverseDigits 10 n = 9 * n

/-- **For $k \ge 2$, the number $11 \cdot (10^k - 1)$ lacks property $P^*$.** For every natural
number $k \ge 2$, the number $11 \cdot (10^k - 1)$ does not have the property $P^*$.

In the source these numbers $1089, 10989, 109989, \dots$ are the basic reverse divisors with
quotient $9$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Lemma 2. -/
theorem_wanted not_hasPropertyPStar_basic_nine (k : ℕ) (hk : 2 ≤ k) :
    ¬ HasPropertyPStar (11 * (10 ^ k - 1))

/-- **No reverse divisor has property $P^*$.** If $n$ is a reverse divisor, then $n$ does not have
the property $P^*$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 4. -/
theorem_wanted not_hasPropertyPStar_of_isReverseDivisor (n : ℕ)
    (h : IsReverseDivisor n) :
    ¬ HasPropertyPStar n

/-- **Infinitely many multiples with divisible reversal.** Let $n$ be a natural number not
divisible by $10$, and suppose that $n$ divides the decimal reversal of $k_0 n$ for some natural
number $k_0 \ge 1$. Then there are infinitely many natural numbers $k \ge 1$ such that $n$
divides the decimal reversal of $k n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 6. -/
theorem_wanted infinite_dvd_reverseDigits_mul (n : ℕ)
    (h10 : ¬ 10 ∣ n)
    (h : ∃ k₀ : ℕ, 1 ≤ k₀ ∧ n ∣ Nat.reverseDigits 10 (k₀ * n)) :
    Set.Infinite
      {k : ℕ | 1 ≤ k ∧ n ∣ Nat.reverseDigits 10 (k * n)}

/-- **Sufficient conditions for a multiple with divisible reversal.** Let $n$ be a natural
number such that $\gcd(n, 10) = 1$, or $n$ equals its decimal reversal, or $n$ is a reverse
divisor. Then there is a natural number $k_0 \ge 1$ such that $n$ divides the decimal reversal
of $k_0 n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 6. -/
theorem_wanted exists_dvd_reverseDigits_mul (n : ℕ)
    (h : Nat.Coprime n 10 ∨ Nat.reverseDigits 10 n = n ∨
      IsReverseDivisor n) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ n ∣ Nat.reverseDigits 10 (k₀ * n)

/-- **Lemma 3**: a non-basic reverse divisor `n` with
quotient `9` begins and ends with the same block
`S_r = 10 9^r 89 = 11 (10^{r+2} - 1)`; if `r = 0`, then
`(11 n)*` begins with `97` and ends with `11`, and if
`r ≥ 1`, then `((10^{r+1} + 1) n)*` (the multiplier
`1 0^r 1`) begins with `98 9^{r-1} 8 = 99·10^r - 2` and
ends with `0^r 11`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
INTEGERS 25 (2025), Article A37, Lemma 3 (`integers-2025-A37-lem-3`). "Non-basic
reverse divisor" is read with quotient `9`, as in the
paper's use of the lemma (proof of Proposition 4); for
quotient `4` the literal claim fails (`21782178` does
not begin with any `S_r`). "Begins with the digit
string `p`" is `x = p·10^t + m` with `m < 10^t`; "ends
with" is a remainder modulo a power of `10`. -/
theorem_wanted reverseDivisor_nine_nonbasic_blocks (n : ℕ)
    (h9 : Nat.reverseDigits 10 n = 9 * n) (hpos : 0 < n)
    (hnb : ∀ r : ℕ, n ≠ 11 * (10 ^ (r + 2) - 1)) :
    (∃ r : ℕ, (∃ t m : ℕ, m < 10 ^ t ∧ n = (11 * (10 ^ (r + 2) - 1)) * 10 ^ t + m) ∧
        n % 10 ^ (r + 4) = 11 * (10 ^ (r + 2) - 1)) ∧
      ∀ r : ℕ, (∃ t m : ℕ, m < 10 ^ t ∧ n = (11 * (10 ^ (r + 2) - 1)) * 10 ^ t + m) →
        n % 10 ^ (r + 4) = 11 * (10 ^ (r + 2) - 1) →
        (r = 0 → (∃ t m : ℕ, m < 10 ^ t ∧ Nat.reverseDigits 10 (11 * n) = 97 * 10 ^ t + m) ∧
            Nat.reverseDigits 10 (11 * n) % 100 = 11) ∧
        (1 ≤ r → (∃ t m : ℕ,
            m < 10 ^ t ∧ Nat.reverseDigits 10 ((10 ^ (r + 1) + 1) * n) =
            (99 * 10 ^ r - 2) * 10 ^ t + m) ∧
            Nat.reverseDigits 10 ((10 ^ (r + 1) + 1) * n) % 10 ^ (r + 2) = 11)

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

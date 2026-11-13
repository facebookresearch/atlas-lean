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

Not stated (see the source audit table): Theorem 2
(the block structure of non-basic quotient-9 reverse
divisors) and Lemma 3, whose digit-block notation
`S_r` is defined only in the paper body.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.Data.Nat.Digits.Reverse

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- **Reverse divisor.** A natural number $n$ is a reverse divisor if $n > 0$ and there is a
natural number $k \ge 2$ such that the decimal reversal of $n$ equals $kn$. Since $n > 0$, such a
$k$ is unique; it is called the quotient of $n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 1 (terminology). -/
def IsReverseDivisor (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, 2 ≤ k ∧ Nat.reverseDigits 10 n = k * n

/-- **Characterization of reverse divisors.** A natural number $n$ is a reverse divisor if and
only if $n > 0$ and there is a natural number $k \ge 2$ such that the decimal reversal of $n$
equals $kn$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 1 (terminology). -/
theorem isReverseDivisor_iff (n : ℕ) :
    IsReverseDivisor n ↔
      0 < n ∧ ∃ k : ℕ, 2 ≤ k ∧ Nat.reverseDigits 10 n = k * n :=
  Iff.rfl

/-- **Property $P^*$.** A natural number $n$ has property $P^*$ if $n$ divides the decimal
reversal of every multiple of $n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 2 (terminology). -/
def HasPropertyPStar (n : ℕ) : Prop :=
  ∀ m : ℕ, n ∣ m → n ∣ Nat.reverseDigits 10 m

/-- **Unfolding property $P^*$.** A natural number $n$ has property $P^*$ if and only if $n$
divides the decimal reversal of every multiple of $n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 2 (terminology). -/
theorem hasPropertyPStar_iff (n : ℕ) :
    HasPropertyPStar n ↔
      ∀ m : ℕ, n ∣ m → n ∣ Nat.reverseDigits 10 m :=
  Iff.rfl

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

/-- **Positive integers sharing a factor with $10$ lack property $P^*$.** If $n \ge 1$ is a
natural number with $\gcd(n, 10) \ne 1$, then $n$ does not have the property $P^*$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 2. -/
theorem_wanted not_hasPropertyPStar_of_not_coprime (n : ℕ)
    (hn : 1 ≤ n) (h : ¬ Nat.Coprime n 10) :
    ¬ HasPropertyPStar n

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

/-- **Basic reverse divisors.** For every natural number $k \ge 2$, the numbers
$11(10^k - 1)$ and $22(10^k - 1)$ both have exactly $k + 2$ decimal digits, the decimal
reversal of $11(10^k - 1)$ equals $9 \cdot 11(10^k - 1)$, and the decimal reversal of
$22(10^k - 1)$ equals $4 \cdot 22(10^k - 1)$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem_wanted basic_reverseDivisors (k : ℕ) (hk : 2 ≤ k) :
    (Nat.digits 10 (11 * (10 ^ k - 1))).length = k + 2 ∧
      Nat.reverseDigits 10 (11 * (10 ^ k - 1)) =
        9 * (11 * (10 ^ k - 1)) ∧
      (Nat.digits 10 (22 * (10 ^ k - 1))).length = k + 2 ∧
      Nat.reverseDigits 10 (22 * (10 ^ k - 1)) =
        4 * (22 * (10 ^ k - 1))

/-- **Reverse divisors have at least four digits.** Every reverse divisor has at least four
decimal digits.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem_wanted four_le_length_digits (n : ℕ)
    (h : IsReverseDivisor n) :
    4 ≤ (Nat.digits 10 n).length

/-- **Reverse divisors with at most seven digits.** Let $n$ be a reverse divisor with $L$
decimal digits, where $L \le 7$. Then $n = 11(10^{L-2} - 1)$ or $n = 22(10^{L-2} - 1)$, where
$L - 2$ is read as $0$ when $L < 2$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem_wanted eq_basic_of_length_le_seven (n : ℕ)
    (h : IsReverseDivisor n)
    (h7 : (Nat.digits 10 n).length ≤ 7) :
    n = 11 * (10 ^ ((Nat.digits 10 n).length - 2) - 1) ∨
      n = 22 * (10 ^ ((Nat.digits 10 n).length - 2) - 1)

/-- **Reverse divisors with quotient $4$ lack property $P^*$.** If $n > 0$ is a natural number
whose decimal reversal equals $4n$, then $n$ does not have the property $P^*$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Lemma 1. -/
theorem_wanted not_hasPropertyPStar_of_quotient_four (n : ℕ)
    (hn : 0 < n) (h : Nat.reverseDigits 10 n = 4 * n) :
    ¬ HasPropertyPStar n

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

/-- **A product congruent to $11$ modulo a power of ten.** For every natural number $r$, let
$a = (10^r - 1) \cdot 100 + 89$, the integer whose decimal digits are $r$ nines followed by $89$,
and let $b = 10^{r+2} - 1$, the integer whose decimal digits are $r + 2$ nines. Then the
remainder of $ab$ modulo $10^{r+2}$ is $11$; that is, the last $r + 2$ decimal digits of $ab$ are
$r$ zeros followed by $11$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Lemma 4. -/
theorem mul_nines_modEq_eleven (r : ℕ) :
    ((10 ^ r - 1) * 100 + 89) * (10 ^ (r + 2) - 1) %
        10 ^ (r + 2) = 11 := by
  have hM : (100 : ℕ) ≤ 10 ^ (r + 2) := by
    calc (100 : ℕ) = 10 ^ 2 := by norm_num
    _ ≤ 10 ^ (r + 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : ((10 ^ r - 1) * 100 + 89 : ℕ) + 11 = 10 ^ (r + 2) := by
    have h1 : 1 ≤ 10 ^ r := Nat.one_le_pow r 10 (by norm_num)
    have h2 : (10 ^ r - 1) * 100 = 10 ^ r * 100 - 100 := by
      rw [Nat.sub_mul, Nat.one_mul]
    rw [h2, pow_add]
    omega
  have hB : (10 ^ (r + 2) - 1 : ℕ) + 1 = 10 ^ (r + 2) :=
    Nat.sub_add_cancel (Nat.one_le_pow _ 10 (by norm_num))
  have hprod : ((10 ^ r - 1) * 100 + 89) * (10 ^ (r + 2) - 1) +
        11 * 10 ^ (r + 2) =
      10 ^ (r + 2) * (10 ^ (r + 2) - 1) + 11 := by
    calc ((10 ^ r - 1) * 100 + 89) * (10 ^ (r + 2) - 1) +
          11 * 10 ^ (r + 2)
        = ((10 ^ r - 1) * 100 + 89) * (10 ^ (r + 2) - 1) +
            11 * ((10 ^ (r + 2) - 1) + 1) := by rw [hB]
    _ = (((10 ^ r - 1) * 100 + 89) + 11) * (10 ^ (r + 2) - 1) + 11 := by
          ring
    _ = 10 ^ (r + 2) * (10 ^ (r + 2) - 1) + 11 := by rw [hA]
  have hmod := congrArg (· % 10 ^ (r + 2)) hprod
  rw [mul_comm 11 (10 ^ (r + 2)), Nat.add_mul_mod_self_left] at hmod
  rw [Nat.add_comm (10 ^ (r + 2) * (10 ^ (r + 2) - 1)) 11,
    Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega : 11 < 10 ^ (r + 2))] at hmod
  exact hmod

/-- **In base $B$, divisors of $B^2 - 1$ divide reversals of their multiples.** Let $B \ge 2$ be
a natural number and let $n$ be a natural number dividing $B^2 - 1$. Then $n$ divides the
base-$B$ reversal of every multiple of $n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 5. -/
theorem_wanted dvd_reverseDigits_of_dvd (B n : ℕ) (hB : 2 ≤ B)
    (hn : n ∣ B ^ 2 - 1) (m : ℕ) (hm : n ∣ m) :
    n ∣ Nat.reverseDigits B m

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

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

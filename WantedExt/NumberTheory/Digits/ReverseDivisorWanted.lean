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

/-- A *reverse divisor* is a positive integer whose
decimal reversal is `k` times it for some `k ≥ 2`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 1 (terminology). -/
def IsReverseDivisor (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, 2 ≤ k ∧ Nat.reverseDigits 10 n = k * n

/-- Characterization of `IsReverseDivisor` by its
defining existential.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 1 (terminology). -/
theorem isReverseDivisor_iff (n : ℕ) :
    IsReverseDivisor n ↔
      0 < n ∧ ∃ k : ℕ, 2 ≤ k ∧ Nat.reverseDigits 10 n = k * n :=
  Iff.rfl

/-- The property `P*`: `n` divides the decimal reversal
of every multiple of `n`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 2 (terminology). -/
def HasPropertyPStar (n : ℕ) : Prop :=
  ∀ m : ℕ, n ∣ m → n ∣ Nat.reverseDigits 10 m

/-- Characterization of `HasPropertyPStar` by its
defining divisibility condition.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Section 2 (terminology). -/
theorem hasPropertyPStar_iff (n : ℕ) :
    HasPropertyPStar n ↔
      ∀ m : ℕ, n ∣ m → n ∣ Nat.reverseDigits 10 m :=
  Iff.rfl

/-- **Theorem 3**: an integer `n ≥ 1` has the property
`P*` if and only if `n` is one of the (positive)
divisors of `99`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 3. -/
theorem_wanted hasPropertyPStar_iff_dvd (n : ℕ) (hn : 1 ≤ n) :
    HasPropertyPStar n ↔ n ∣ 99

/-- **Proposition 1**: the positive divisors of `99`
have the property `P*`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 1. -/
theorem_wanted hasPropertyPStar_of_dvd (n : ℕ) (hn : n ∣ 99) :
    HasPropertyPStar n

/-- **Proposition 2**: if an integer `n ≥ 1` is not
coprime with `10`, then it does not have the property
`P*`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 2. -/
theorem_wanted not_hasPropertyPStar_of_not_coprime (n : ℕ)
    (hn : 1 ≤ n) (h : ¬ Nat.Coprime n 10) :
    ¬ HasPropertyPStar n

/-- **Proposition 3**: no palindrome other than
`1, 3, 9, 11, 33` and `99` has the property `P*`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 3. -/
theorem_wanted palindrome_hasPropertyPStar (n : ℕ) (hn : 1 ≤ n)
    (hpal : Nat.reverseDigits 10 n = n) (h : HasPropertyPStar n) :
    n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 11 ∨ n = 33 ∨ n = 99

/-- **Theorem 1**, quotient classification: the quotient
of a reverse divisor is either `4` or `9`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem_wanted reverseDigits_eq_four_or_nine_mul (n : ℕ)
    (h : IsReverseDivisor n) :
    Nat.reverseDigits 10 n = 4 * n ∨ Nat.reverseDigits 10 n = 9 * n

/-- **Theorem 1**, basic examples: for `k ≥ 2`, the
`(k + 2)`-digit numbers `11 * (10^k - 1)` and
`22 * (10^k - 1)` are reverse divisors with respective
quotients `9` and `4`.

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

/-- **Theorem 1**, minimum size: no reverse divisor has
fewer than four digits.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem_wanted four_le_length_digits (n : ℕ)
    (h : IsReverseDivisor n) :
    4 ≤ (Nat.digits 10 n).length

/-- **Theorem 1**, uniqueness in small lengths: for
`4`, `5`, `6` or `7` digits, the basic examples are the
only reverse divisors.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Theorem 1 (quoted from the literature). -/
theorem_wanted eq_basic_of_length_le_seven (n : ℕ)
    (h : IsReverseDivisor n)
    (h7 : (Nat.digits 10 n).length ≤ 7) :
    n = 11 * (10 ^ ((Nat.digits 10 n).length - 2) - 1) ∨
      n = 22 * (10 ^ ((Nat.digits 10 n).length - 2) - 1)

/-- **Lemma 1**: no reverse divisor with quotient `4`
has the property `P*`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Lemma 1. -/
theorem_wanted not_hasPropertyPStar_of_quotient_four (n : ℕ)
    (hn : 0 < n) (h : Nat.reverseDigits 10 n = 4 * n) :
    ¬ HasPropertyPStar n

/-- **Lemma 2**: no basic reverse divisor with quotient
`9` has the property `P*`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Lemma 2. -/
theorem_wanted not_hasPropertyPStar_basic_nine (k : ℕ) (hk : 2 ≤ k) :
    ¬ HasPropertyPStar (11 * (10 ^ k - 1))

/-- **Proposition 4**: no reverse divisor has the
property `P*`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 4. -/
theorem_wanted not_hasPropertyPStar_of_isReverseDivisor (n : ℕ)
    (h : IsReverseDivisor n) :
    ¬ HasPropertyPStar n

/-- **Lemma 4**: the product of the integer consisting
of `r` digits `9` followed by `89` with the integer
consisting of `r + 2` digits `9` ends with `r` digits
`0` followed by `11`; that is, it is congruent to `11`
modulo `10^{r+2}`.

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

/-- **Proposition 5**: in base `B ≥ 2`, every positive
divisor of `B^2 - 1` has the base-`B` property `P_B*`:
it divides the base-`B` reversal of each of its
multiples.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 5. -/
theorem_wanted dvd_reverseDigits_of_dvd (B n : ℕ) (hB : 2 ≤ B)
    (hn : n ∣ B ^ 2 - 1) (m : ℕ) (hm : n ∣ m) :
    n ∣ Nat.reverseDigits B m

/-- **Proposition 6**: if `10 ∤ n` and there exists
`k₀ ≥ 1` with `n ∣ reverse(k₀ * n)`, then there are
infinitely many `k ≥ 1` with `n ∣ reverse(k * n)`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 6. -/
theorem_wanted infinite_dvd_reverseDigits_mul (n : ℕ)
    (h10 : ¬ 10 ∣ n)
    (h : ∃ k₀ : ℕ, 1 ≤ k₀ ∧ n ∣ Nat.reverseDigits 10 (k₀ * n)) :
    Set.Infinite
      {k : ℕ | 1 ≤ k ∧ n ∣ Nat.reverseDigits 10 (k * n)}

/-- **Proposition 6**, sufficient conditions: the
hypothesis of Proposition 6 is satisfied if
`gcd(n, 10) = 1`, or if `n` is a palindrome, or if `n`
is a reverse divisor.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 6. -/
theorem_wanted exists_dvd_reverseDigits_mul (n : ℕ)
    (h : Nat.Coprime n 10 ∨ Nat.reverseDigits 10 n = n ∨
      IsReverseDivisor n) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ n ∣ Nat.reverseDigits 10 (k₀ * n)

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

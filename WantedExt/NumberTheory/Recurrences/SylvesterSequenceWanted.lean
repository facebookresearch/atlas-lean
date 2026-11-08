/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A note on Sylvester's sequence

Statements from Abderrahim Makki Naciri, "A Note on Sylvester's
Sequence", *INTEGERS* 24 (2024), Article A117
(<https://math.colgate.edu/~integers/y117/y117.pdf>).

The classical Sylvester sequence starts with `S₀ = 2` and satisfies
`Sₙ₊₁ = Sₙ(Sₙ - 1) + 1`.  This is exactly
`Nat.generalizedSylvester 1` from MathlibExt, whose parameter gives
initial value `1 + 1 = 2` and the same recurrence.

Proposition 1, Proposition 2, and Corollary 1 are split into their
atomic congruence, divisibility, and classification claims.
Proposition 3 is split into its perfect-power and `a^m ± 1` claims.
The quoted Theorem 1 is F. Luca, Sz. Tengely, and A. Togbé,
"On the Diophantine equation `x² + C = 4yⁿ`", *Annales des Sciences
Mathématiques du Québec* 33(2) (2009), 171--184, Theorem 1.1, for
`C = 3` and `C = 7`, as quoted by Naciri.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.GeneralizedSylvester

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

/-- The classical Sylvester sequence `2, 3, 7, 43, …`, as the
parameter-`1` case of MathlibExt's generalized Sylvester sequence. -/
abbrev sylvesterNumber (n : ℕ) : ℕ :=
  Nat.generalizedSylvester 1 n

/-- **Proposition 1, divisibility**: for positive `k` and `m n ≥ k`,
`(S_k - 1)^2` divides `S_n - S_m` over `ℤ`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, divisibility (4). -/
theorem_wanted sylvester_sub_dvd
    (k m n : ℕ) (hk : 1 ≤ k) (hm : k ≤ m) (hn : k ≤ n) :
    ((sylvesterNumber k : ℤ) - 1) ^ 2 ∣
      (sylvesterNumber n : ℤ) - (sylvesterNumber m : ℤ)

/-- **Proposition 1, congruence (5)**: `S_n ≡ 3 (mod 4)` for `n ≥ 1`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (5). -/
theorem_wanted sylvester_modEq_three_mod_four
    (n : ℕ) (hn : 1 ≤ n) :
    sylvesterNumber n % 4 = 3

/-- **Proposition 1, congruence (6)**: `S_n ≡ 7 (mod 36)` for
`n ≥ 2`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (6). -/
theorem_wanted sylvester_modEq_seven_mod_thirty_six
    (n : ℕ) (hn : 2 ≤ n) :
    sylvesterNumber n % 36 = 7

/-- **Proposition 1, congruence (7)**: `S_n ≡ 43 (mod 1764)` for
`n ≥ 3`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (7). -/
theorem_wanted sylvester_modEq_forty_three_mod_1764
    (n : ℕ) (hn : 3 ≤ n) :
    sylvesterNumber n % 1764 = 43

/-- **Proposition 2, divisibility**: for positive `k` and `n ≥ k`,
`S_k^2 + 1` divides `S_n - (-1)^(n-k) S_k` over `ℤ`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 2, divisibility (8). -/
theorem_wanted sylvester_sq_add_one_dvd_sub
    (k n : ℕ) (hk : 1 ≤ k) (hn : k ≤ n) :
    (sylvesterNumber k : ℤ) ^ 2 + 1 ∣
      (sylvesterNumber n : ℤ) -
        (-1 : ℤ) ^ (n - k) * (sylvesterNumber k : ℤ)

/-- **Proposition 2, congruence (9), even indices**:
`S_{2i} ≡ 7 (mod 10)` for `i ≥ 1`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 2, congruence (9), even indices. -/
theorem_wanted sylvester_even_index_mod_ten
    (i : ℕ) (hi : 1 ≤ i) :
    sylvesterNumber (2 * i) % 10 = 7

/-- **Proposition 2, congruence (9), odd indices**:
`S_{2i+1} ≡ 3 (mod 10)` for `i ≥ 1`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 2, congruence (9), odd indices. -/
theorem_wanted sylvester_odd_index_mod_ten
    (i : ℕ) (hi : 1 ≤ i) :
    sylvesterNumber (2 * i + 1) % 10 = 3

/-- **Corollary 1(a)**: the Mersenne values `2^r - 1` (`r ≥ 1`) hit
by the Sylvester sequence are exactly `3` and `7`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(a). -/
theorem_wanted mersenne_sylvester_values_eq :
    {x : ℕ | ∃ n r : ℕ, 1 ≤ r ∧ x = sylvesterNumber n ∧
      x = 2 ^ r - 1} = {3, 7}

/-- **Corollary 1(b)**: the triangular values hit by the Sylvester
sequence are exactly `3`.  Triangular is encoded without division by
`2 * x = m * (m + 1)` for positive `m`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(b). -/
theorem_wanted triangular_sylvester_values_eq :
    {x : ℕ | ∃ n m : ℕ, 1 ≤ m ∧ x = sylvesterNumber n ∧
      2 * x = m * (m + 1)} = {3}

/-- **Corollary 1(c)**: no Sylvester number is a perfect number.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(c). -/
theorem_wanted sylvester_not_perfect
    (n : ℕ) :
    ¬ (sylvesterNumber n).Perfect

/-- **Corollary 1(d)**: every Sylvester number after `S₀ = 2` has a
prime divisor congruent to `3` modulo `4`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(d). -/
theorem_wanted sylvester_exists_prime_divisor_mod_four_eq_three
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ sylvesterNumber n ∧ p % 4 = 3

/-- **Proposition 3(a)**: no Sylvester number is a perfect power
`a^m` with `a ≥ 2` and `m ≥ 2`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 3(a). -/
theorem_wanted sylvester_not_perfect_power
    (n : ℕ) :
    ¬ ∃ a m : ℕ, 2 ≤ a ∧ 2 ≤ m ∧ sylvesterNumber n = a ^ m

/-- **Proposition 3(b)**: apart from `S₁` and `S₂`, no Sylvester
number has the form `a^m ± 1` with `a ≥ 2` and `m ≥ 2`.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 3(b). -/
theorem_wanted sylvester_ne_pow_add_or_sub_one
    (n : ℕ) (hn1 : n ≠ 1) (hn2 : n ≠ 2) :
    ¬ ∃ a m : ℕ, 2 ≤ a ∧ 2 ≤ m ∧
      ((sylvesterNumber n : ℤ) = (a : ℤ) ^ m + 1 ∨
        (sylvesterNumber n : ℤ) = (a : ℤ) ^ m - 1)

/-- **Theorem 1, `C = 3`** (Luca--Tengely--Togbé, quoted by Naciri):
the positive coprime solutions of `x² + 3 = 4yⁿ` with `n ≥ 3` are
exactly `x = y = 1` (any `n ≥ 3`) and `(n, x, y) = (3, 37, 7)`.

Source: F. Luca, Sz. Tengely, and A. Togbé, "On the Diophantine equation x² + C = 4yⁿ", Theorem 1.1, as quoted in Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Theorem 1, equation with C = 3. -/
theorem_wanted lebesgue_nagell_three_solutions_iff
    (n x y : ℕ) :
    (3 ≤ n ∧ 1 ≤ x ∧ 1 ≤ y ∧ Nat.Coprime x y ∧
        x ^ 2 + 3 = 4 * y ^ n) ↔
      (3 ≤ n ∧ ((x = 1 ∧ y = 1) ∨ (n = 3 ∧ x = 37 ∧ y = 7)))

/-- **Theorem 1, `C = 7`** (Luca--Tengely--Togbé, quoted by Naciri):
the positive coprime solutions of `x² + 7 = 4yⁿ` with `n ≥ 3` are
exactly `(n, x, y) = (3, 5, 2)`, `(5, 11, 2)`, and `(13, 181, 2)`.

Source: F. Luca, Sz. Tengely, and A. Togbé, "On the Diophantine equation x² + C = 4yⁿ", Theorem 1.1, as quoted in Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Theorem 1, equation with C = 7. -/
theorem_wanted lebesgue_nagell_seven_solutions_iff
    (n x y : ℕ) :
    (3 ≤ n ∧ 1 ≤ x ∧ 1 ≤ y ∧ Nat.Coprime x y ∧
        x ^ 2 + 7 = 4 * y ^ n) ↔
      ((n = 3 ∧ x = 5 ∧ y = 2) ∨ (n = 5 ∧ x = 11 ∧ y = 2) ∨
        (n = 13 ∧ x = 181 ∧ y = 2))

end MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

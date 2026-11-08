/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quotients of a more general theorem of Wilson

Statements from Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", *INTEGERS* 25 (2025), Article A93
(<https://math.colgate.edu/~integers/z93/z93.pdf>).

Non-composite means `1` or prime.  Congruences for the rational
numbers `Z` and `Z+` are stated through the integer values whose
existence is asserted in the corresponding integrality theorems;
Theorem 6 is stated in the usual rational form that the numerator
of the difference is divisible by `p`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.WilsonQuotientsWanted

/-- Morozov's Wilson-like quotient
`M_k(n) = (1 + (-1) ^ k * k ! * (n - k - 1)!) / n` in `ℚ`. -/
def wilsonQuotientM (k n : ℕ) : ℚ :=
  (1 + (-1 : ℚ) ^ k * (Nat.factorial k * Nat.factorial (n - k - 1) : ℚ)) / n

/-- Morozov's sign-adjusted quotient
`M_k^+(n) = ((-1) ^ k + k ! * (n - k - 1)!) / n` in `ℚ`. -/
def wilsonQuotientMPlus (k n : ℕ) : ℚ :=
  ((-1 : ℚ) ^ k + (Nat.factorial k * Nat.factorial (n - k - 1) : ℚ)) / n

/-- Morozov's sum `Z(n) = ∑ k ∈ [0,n), M_k(n)`. -/
def wilsonQuotientZ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, wilsonQuotientM k n

/-- Morozov's sum `Z^+(n) = ∑ k ∈ [0,n), M_k^+(n)`. -/
def wilsonQuotientZPlus (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, wilsonQuotientMPlus k n

/-- Morozov's Corollary 1: for `1 ≤ n` and `k < n`,
`(-1) ^ k * k ! * (n - k - 1)! ≡ -1 [ZMOD n]` if and only if
`n` is `1` or prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Corollary 1. -/
theorem_wanted neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff
    (n k : ℕ) (hn : 1 ≤ n) (hk : k < n) :
    ((-1 : ℤ) ^ k * (Nat.factorial k * Nat.factorial (n - k - 1) : ℤ) ≡
        -1 [ZMOD (n : ℤ)]) ↔
      n = 1 ∨ n.Prime

/-- Morozov's Theorem 1: `Z(n)` is an integer for positive `n`.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 1. -/
theorem_wanted exists_int_eq_wilsonQuotientZ
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ n

/-- Morozov's Theorem 2: `Z^+(n)` is a natural number if and
only if `n` is even or `1` or prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 2. -/
theorem_wanted exists_nat_eq_wilsonQuotientZPlus_iff
    (n : ℕ) (hn : 1 ≤ n) :
    (∃ m : ℕ, (m : ℚ) = wilsonQuotientZPlus n) ↔
      n % 2 = 0 ∨ n = 1 ∨ n.Prime

/-- Morozov's Theorem 3: the integer value of `Z(n)` is
`1 [ZMOD n]` for composite `n` and `-1 [ZMOD n]` for `n = 1`
or prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 3. -/
theorem_wanted exists_int_eq_wilsonQuotientZ_and_modEq
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ n ∧
      ((¬(n = 1 ∨ n.Prime) → z ≡ 1 [ZMOD (n : ℤ)]) ∧
        ((n = 1 ∨ n.Prime) → z ≡ -1 [ZMOD (n : ℤ)]))

/-- Morozov's Theorem 4: the integer value of `Z(2n - 1)` is
`0 [ZMOD n]` if and only if `n` is `1` or prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 4. -/
theorem_wanted exists_int_eq_wilsonQuotientZ_two_mul_sub_one_modEq_zero_iff
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ (2 * n - 1) ∧
      ((z ≡ 0 [ZMOD (n : ℤ)]) ↔ n = 1 ∨ n.Prime)

/-- Morozov's Theorem 5: for the integer value of `Z^+(2n)`,
it is `0 [ZMOD 2n]` when `n = 2` or `n` is composite, and
`n + 1 [ZMOD 2n]` when `n` is an odd prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 5, equations (8) and (9). -/
theorem_wanted exists_int_eq_wilsonQuotientZPlus_two_mul_and_modEq
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZPlus (2 * n) ∧
      (((n = 2 ∨ ¬(n = 1 ∨ n.Prime)) → z ≡ 0 [ZMOD (2 * n : ℤ)]) ∧
        (((n.Prime ∧ n ≠ 2) → z ≡ (n : ℤ) + 1 [ZMOD (2 * n : ℤ)])))

/-- Morozov's Theorem 6 in corrected form: for an odd prime
`p`, `Z^+(p)` is congruent modulo `p` to
`B_{2(p-1)} - B_{p-1} - ∑ k ∈ [0,p), (-1) ^ k * H_k`, in the
rational sense that `p` divides the numerator of the difference.

This is the congruence obtained by summing the paper's
Equation (7). The printed simplification of the alternating
harmonic sum to `H_{p-1} / 2` is false already at `p = 3`.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 6 and Equation (7). -/
theorem_wanted prime_dvd_num_wilsonQuotientZPlus_sub_bernoulli_alternating
    (p : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1) :
    (p : ℤ) ∣ (wilsonQuotientZPlus p -
      (bernoulli (2 * (p - 1)) - bernoulli (p - 1) -
        ∑ k ∈ Finset.range p, (-1 : ℚ) ^ k * harmonic k)).num

end MathlibExt.NumberTheory.WilsonQuotientsWanted

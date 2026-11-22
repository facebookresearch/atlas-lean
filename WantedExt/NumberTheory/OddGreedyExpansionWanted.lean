/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rational numbers with two-term odd greedy expansion

Statements from Joel Louwsma and Joseph Martino,
"Rational Numbers with Two-Term Odd Greedy Expansion",
*INTEGERS* 25 (2025), Article A46
(<https://math.colgate.edu/~integers/vol25.html>).

The odd greedy expansion of a positive rational is its
greedy Egyptian expansion using only odd denominators;
its first denominator is the odd greedy choice
`MetaMathlibExt.IsOddGreedyChoice` (shared with the odd
greedy expansion termination conjecture). Lemma 2's
characterization was verified against this definition
for `n, d < 60`, and Proposition 1 on thousands of
random examples. Theorem 3 and Corollary 5 were checked
by brute force against the odd greedy algorithm for
reduced fractions with numerator at most 30 and
denominator at most 1500.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.OddGreedyChoice

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.OddGreedyExpansionWanted

/-- **Proposition 1**: if a rational number is the sum
of an even number of unit fractions with odd
denominators, then every fraction representing it has
even numerator.

Source: Joel Louwsma and Joseph Martino, "Rational
Numbers with Two-Term Odd Greedy Expansion",
Proposition 1. -/
theorem_wanted even_num_of_even_sum_unit_fractions
    (m : ℕ) (hm : Even m) (d : Fin m → ℕ)
    (hd : ∀ i, Odd (d i)) (a b : ℤ) (hb : b ≠ 0)
    (h : (a : ℚ) / (b : ℚ) = ∑ i, (1 : ℚ) / (d i : ℚ)) :
    Even a

/-- **Lemma 2**: for positive integers `n, d` and odd
`x₁`, `x₁` is the first denominator of the odd greedy
expansion of `n / d` if and only if
`0 ≤ n * x₁ - d < 2 * n`.

Source: Joel Louwsma and Joseph Martino, "Rational
Numbers with Two-Term Odd Greedy Expansion", Lemma 2. -/
theorem_wanted isOddGreedyChoice_iff (n d x1 : ℕ)
    (hn : 0 < n) (hd : 0 < d) (hx : Odd x1) :
    MetaMathlibExt.IsOddGreedyChoice ((n : ℚ) / (d : ℚ)) x1 ↔
      d ≤ n * x1 ∧ n * x1 < d + 2 * n

/-- **Theorem 3**: a positive rational has a two-term odd greedy expansion if and only
if it equals `n / (n (∏_{p ∣ r} p^{a_p}) (1 + 2t) - r)` for an even positive `n`, an
integer `0 < r < 2n` with `v₂(2r) ≤ v₂(n)`, a nonnegative integer `t`, and
`a_p = max(⌈(v_p(2r) - v_p(n)) / 2⌉, 0)`.

Stated for the value of the fraction (the expansion depends only on it); "two terms" is
the odd greedy choice `x₁`, then the odd greedy choice `x₂` of the remainder, leaving
remainder `0`. The exponent is written in `ℕ` as `(v_p(2r) - v_p(n) + 1) / 2` with
truncated subtraction, which equals `max(⌈(v_p(2r) - v_p(n)) / 2⌉, 0)`.

Source: Joel Louwsma and Joseph Martino, *Rational Numbers with Two-Term Odd Greedy
Expansion*, INTEGERS 25 (2025), Article A46, Theorem 3 (`integers-2025-A46-thm-3`). -/
theorem_wanted twoTermOddGreedy_iff (q : ℚ) :
    (∃ x₁ x₂ : ℕ, MetaMathlibExt.IsOddGreedyChoice q x₁ ∧
        MetaMathlibExt.IsOddGreedyChoice (q - 1 / (x₁ : ℚ)) x₂ ∧
          q - 1 / (x₁ : ℚ) - 1 / (x₂ : ℚ) = 0) ↔
      ∃ n r t : ℕ, Even n ∧ 0 < r ∧ r < 2 * n ∧
        padicValNat 2 (2 * r) ≤ padicValNat 2 n ∧
        q = (n : ℚ) / (((n * (∏ p ∈ r.primeFactors,
          p ^ ((padicValNat p (2 * r) - padicValNat p n + 1) / 2)) * (1 + 2 * t) : ℕ) : ℚ) -
            (r : ℚ))

/-- **Corollary 5**: a positive fraction `a / b` in reduced form has a two-term odd
greedy expansion if and only if `a` is even and
`b = a (∏_{p ∣ r} p^{⌈v_p(r)/2⌉}) (1 + 2t) - r` for a positive integer `r < 2a`
coprime to `2a` and a nonnegative integer `t`.

"Two terms" is as in Theorem 3; `⌈v_p(r)/2⌉` is written `(v_p(r) + 1) / 2` in `ℕ`.
Positivity of `a` and `b` is not assumed: both sides fail when `a = 0` or `b = 0`.

Source: Joel Louwsma and Joseph Martino, *Rational Numbers with Two-Term Odd Greedy
Expansion*, INTEGERS 25 (2025), Article A46, Corollary 5 (`integers-2025-A46-cor-5`). -/
theorem_wanted twoTermOddGreedy_reduced_iff (a b : ℕ) (hab : Nat.Coprime a b) :
    (∃ x₁ x₂ : ℕ, MetaMathlibExt.IsOddGreedyChoice ((a : ℚ) / (b : ℚ)) x₁ ∧
        MetaMathlibExt.IsOddGreedyChoice ((a : ℚ) / (b : ℚ) - 1 / (x₁ : ℚ)) x₂ ∧
          (a : ℚ) / (b : ℚ) - 1 / (x₁ : ℚ) - 1 / (x₂ : ℚ) = 0) ↔
      Even a ∧ ∃ r t : ℕ, 0 < r ∧ r < 2 * a ∧ Nat.Coprime r (2 * a) ∧
        (b : ℤ) = ((a * (∏ p ∈ r.primeFactors, p ^ ((padicValNat p r + 1) / 2)) *
          (1 + 2 * t) : ℕ) : ℤ) - (r : ℤ)

end MathlibExt.NumberTheory.OddGreedyExpansionWanted

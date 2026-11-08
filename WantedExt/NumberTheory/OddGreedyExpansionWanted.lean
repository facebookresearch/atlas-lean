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
random examples.

Not stated (see the source audit table): Theorem 3 and
Corollary 5, whose displayed forms are garbled in the
extracted statements.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Defs
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

end MathlibExt.NumberTheory.OddGreedyExpansionWanted

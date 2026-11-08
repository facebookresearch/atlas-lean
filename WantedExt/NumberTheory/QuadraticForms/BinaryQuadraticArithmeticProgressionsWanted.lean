/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arithmetic progressions represented by binary quadratic forms

Statements from Ajai Choudhry, "Arithmetic Progressions
Represented by Binary Quadratic Forms", *INTEGERS* 25 (2025),
Article A14 (<https://math.colgate.edu/~integers/z14/z14.pdf>).

Irreducibility of an integral binary quadratic form is used in
the paper's sense that its discriminant is not a perfect square.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

/-- Choudhry's Lemma 1: if every term of a rational arithmetic
progression is represented over `ℚ` by an integral binary
quadratic form, then after scaling by a nonzero square `k ^ 2`
every term is represented over `ℤ` by the same form.

The nonzero condition on `k` is the paper's common-denominator
choice; it also excludes the trivial zero scaling.

Source: Ajai Choudhry, "Arithmetic Progressions Represented by
Binary Quadratic Forms", Lemma 1. -/
theorem_wanted exists_int_representations_of_rat_arithmetic_progression
    (a b c : ℤ) (n : ℕ) (u0 d : ℚ)
    (hrep : ∀ i ∈ Finset.range n, ∃ x y : ℚ,
      (a : ℚ) * x ^ 2 + (b : ℚ) * x * y + (c : ℚ) * y ^ 2 =
        u0 + i * d) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ i ∈ Finset.range n, ∃ x y : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2 : ℚ) =
        (k : ℚ) ^ 2 * (u0 + i * d)

/-- Choudhry's Theorem 1: with
`u₁ = 4p⁵g¹⁰ - 47p⁴qg⁸h² - 156p³q²g⁶h⁴ + 2052p²q³g⁴h⁶
      + 4833pq⁴g²h⁸ + 324q⁵h¹⁰` and
`d = 12pqg²h²(pg² - 3qh²)(pg² + 6qh²)(2pg² + 3qh²)`,
all nine terms `u₁ + i * d` (`i < 9`) are represented by
`p * x ^ 2 + q * y ^ 2`, provided `-4 * p * q` is not a square.

Source: Ajai Choudhry, "Arithmetic Progressions Represented by
Binary Quadratic Forms", Theorem 1, relations (3.1). -/
theorem_wanted exists_representation_nine_term_diagonal_quadratic
    (p q g h : ℤ) (hirr : ¬IsSquare (-4 * p * q)) :
    ∀ i : ℕ, i < 9 → ∃ x y : ℤ,
      (4 * p ^ 5 * g ^ 10 - 47 * p ^ 4 * q * g ^ 8 * h ^ 2 -
          156 * p ^ 3 * q ^ 2 * g ^ 6 * h ^ 4 +
          2052 * p ^ 2 * q ^ 3 * g ^ 4 * h ^ 6 +
          4833 * p * q ^ 4 * g ^ 2 * h ^ 8 + 324 * q ^ 5 * h ^ 10) +
        i * (12 * p * q * g ^ 2 * h ^ 2 *
          (p * g ^ 2 - 3 * q * h ^ 2) * (p * g ^ 2 + 6 * q * h ^ 2) *
          (2 * p * g ^ 2 + 3 * q * h ^ 2)) =
        p * x ^ 2 + q * y ^ 2

/-- Choudhry's Theorem 2: every integral binary quadratic form
whose discriminant is not a perfect square represents a
nine-term arithmetic progression with nonzero common difference.

The nonzero-difference clause records the intended parametric
construction and excludes the constant zero progression.

Source: Ajai Choudhry, "Arithmetic Progressions Represented by
Binary Quadratic Forms", Theorem 2. -/
theorem_wanted exists_nine_term_arithmetic_progression_binary_quadratic
    (a b c : ℤ) (hirr : ¬IsSquare (b ^ 2 - 4 * a * c)) :
    ∃ u0 d : ℤ, d ≠ 0 ∧ ∀ i : ℕ, i < 9 → ∃ x y : ℤ,
      u0 + i * d = a * x ^ 2 + b * x * y + c * y ^ 2

end MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

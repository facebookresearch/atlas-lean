/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Rat.Defs
import Mathlib.Basic.Finite.Sum
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Choose
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Arithmetic progressions represented by binary quadratic forms

A common denominator for both coordinates of every representation scales a finite
arithmetic progression by its square. The ATLAS wiki attributes this result to Ajai
Choudhry's “Arithmetic Progressions Represented by Binary Quadratic Forms”.

The wiki attributes to the same paper an explicit nine-term arithmetic progression, whose first
term `u₁` and common difference `d` are polynomials in integers `p, q, g, h`, with every term
represented by `p x ^ 2 + q y ^ 2` when `-4 p q` is not a perfect square. With `P = p g ^ 2` and
`Q = q h ^ 2`, both `u₁` and `d` are binary quintic forms in `P` and `Q`. The proof below checks
polynomial identities, so it does not use the hypothesis on `-4 p q`: the term with index
`3 j + k`, where `j, k < 3`, equals `P X_j ^ 2 + Q Y_k ^ 2` for integral binary quadratic forms
`X_j` and `Y_k` in `P` and `Q`, because the values `P X_j ^ 2` and `Q Y_k ^ 2` run through
three-term arithmetic progressions with common differences `3 d` and `d` whose first terms add
up to `u₁`.
-/

public section

namespace MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

/-- If an integral binary quadratic form represents each term of a finite arithmetic
progression over the rationals, then it represents every term over the integers after
multiplying the progression by a single nonzero integer square.

Source: Ajai Choudhry, "Arithmetic Progressions Represented by
Binary Quadratic Forms", Lemma 1. -/
theorem exists_int_representations_of_rat_arithmetic_progression
    (a b c : ℤ) (n : ℕ) (u0 d : ℚ)
    (hrep : ∀ i ∈ Finset.range n, ∃ x y : ℚ,
      (a : ℚ) * x ^ 2 + (b : ℚ) * x * y + (c : ℚ) * y ^ 2 =
        u0 + i * d) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ i ∈ Finset.range n, ∃ x y : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2 : ℚ) =
        (k : ℚ) ^ 2 * (u0 + i * d) := by
  choose x y hxy using fun i : Fin n => hrep i (Finset.mem_range.mpr i.isLt)
  -- Index both families of coordinates together to clear all denominators at once.
  obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (Sum.elim x y)
  refine ⟨k, nonZeroDivisors.coe_ne_zero k, ?_⟩
  intro i hi
  let j : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨X, hX⟩ := hk (Sum.inl j)
  obtain ⟨Y, hY⟩ := hk (Sum.inr j)
  refine ⟨X, Y, ?_⟩
  simp only [eq_intCast, zsmul_eq_mul, Sum.elim_inl, Sum.elim_inr] at hX hY
  rw [hX, hY, ← hxy j]
  ring

-- The representations below exist for all `p, q, g, h`, so `hirr` is unused; it is kept
-- from the source statement.
set_option linter.unusedVariables false in
/-- **Nine-term arithmetic progressions represented by $px^2 + qy^2$.** Let $p, q, g, h$ be
integers such that $-4pq$ is not a perfect square, and put

$$
u_1 = 4p^5g^{10} - 47p^4qg^8h^2 - 156p^3q^2g^6h^4 + 2052p^2q^3g^4h^6 +
4833pq^4g^2h^8 + 324q^5h^{10}
$$

and

$$
d = 12pqg^2h^2(pg^2 - 3qh^2)(pg^2 + 6qh^2)(2pg^2 + 3qh^2).
$$

Then for every natural number $i < 9$ there are integers $x, y$ with $u_1 + id = px^2 + qy^2$.

Source: Ajai Choudhry, "Arithmetic Progressions Represented by
Binary Quadratic Forms", Theorem 1, relations (3.1). -/
theorem exists_representation_nine_term_diagonal_quadratic
    (p q g h : ℤ) (hirr : ¬IsSquare (-4 * p * q)) :
    ∀ i : ℕ, i < 9 → ∃ x y : ℤ,
      (4 * p ^ 5 * g ^ 10 - 47 * p ^ 4 * q * g ^ 8 * h ^ 2 -
          156 * p ^ 3 * q ^ 2 * g ^ 6 * h ^ 4 +
          2052 * p ^ 2 * q ^ 3 * g ^ 4 * h ^ 6 +
          4833 * p * q ^ 4 * g ^ 2 * h ^ 8 + 324 * q ^ 5 * h ^ 10) +
        i * (12 * p * q * g ^ 2 * h ^ 2 *
          (p * g ^ 2 - 3 * q * h ^ 2) * (p * g ^ 2 + 6 * q * h ^ 2) *
          (2 * p * g ^ 2 + 3 * q * h ^ 2)) =
        p * x ^ 2 + q * y ^ 2 := by
  intro i hi
  set d := 12 * p * q * g ^ 2 * h ^ 2 * (p * g ^ 2 - 3 * q * h ^ 2) *
    (p * g ^ 2 + 6 * q * h ^ 2) * (2 * p * g ^ 2 + 3 * q * h ^ 2) with hd
  -- Write `i = 3 j + k` with `j, k < 3`. The witnesses are `x = g X_j` and `y = h Y_k` for
  -- quadratic forms `X_j`, `Y_k` in `p g ^ 2` and `q h ^ 2`: the values `p x ^ 2` run through a
  -- progression with common difference `3 d`, the values `q y ^ 2` through one with common
  -- difference `d`, and their first terms add up to the first term of the progression.
  obtain ⟨j, hj, k, hk, rfl⟩ : ∃ j < 3, ∃ k < 3, i = 3 * j + k :=
    ⟨i / 3, by omega, i % 3, by omega, by omega⟩
  obtain ⟨x, hx⟩ : ∃ x : ℤ, p * x ^ 2 =
      p * (g * (2 * p ^ 2 * g ^ 4 - 12 * p * q * g ^ 2 * h ^ 2 - 63 * q ^ 2 * h ^ 4)) ^ 2 +
        3 * j * d := by
    interval_cases j
    · exact ⟨g * (2 * p ^ 2 * g ^ 4 - 12 * p * q * g ^ 2 * h ^ 2 - 63 * q ^ 2 * h ^ 4), by simp⟩
    · exact ⟨g * (2 * p ^ 2 * g ^ 4 + 6 * p * q * g ^ 2 * h ^ 2 + 45 * q ^ 2 * h ^ 4), by
        rw [hd]; push_cast; ring⟩
    · exact ⟨g * (2 * p ^ 2 * g ^ 4 + 24 * p * q * g ^ 2 * h ^ 2 - 9 * q ^ 2 * h ^ 4), by
        rw [hd]; push_cast; ring⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, q * y ^ 2 =
      q * (h * (p ^ 2 * g ^ 4 - 24 * p * q * g ^ 2 * h ^ 2 - 18 * q ^ 2 * h ^ 4)) ^ 2 +
        k * d := by
    interval_cases k
    · exact ⟨h * (p ^ 2 * g ^ 4 - 24 * p * q * g ^ 2 * h ^ 2 - 18 * q ^ 2 * h ^ 4), by simp⟩
    · exact ⟨h * (5 * p ^ 2 * g ^ 4 + 6 * p * q * g ^ 2 * h ^ 2 + 18 * q ^ 2 * h ^ 4), by
        rw [hd]; push_cast; ring⟩
    · exact ⟨h * (7 * p ^ 2 * g ^ 4 + 12 * p * q * g ^ 2 * h ^ 2 - 18 * q ^ 2 * h ^ 4), by
        rw [hd]; push_cast; ring⟩
  refine ⟨x, y, ?_⟩
  rw [hx, hy]
  push_cast
  ring

end MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

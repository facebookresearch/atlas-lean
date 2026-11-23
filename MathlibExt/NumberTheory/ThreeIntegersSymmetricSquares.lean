/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.Identities

/-! # Quotients of sums of two rational squares -/

@[expose] public section

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

/-- **Sums of two rational squares.** A rational number $q$ is a sum of two squares when
$q = x^2 + y^2$ for some rational numbers $x$ and $y$. -/
def IsSumTwoSquaresℚ (q : ℚ) : Prop :=
  ∃ x y : ℚ, q = x ^ 2 + y ^ 2

/-- **Quotients of sums of two rational squares.** If $\alpha$ and $\beta$ are nonzero rational
numbers that are each a sum of two squares of rational numbers, then $\alpha / \beta$ is also a
sum of two squares of rational numbers.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Lemma 1. -/
theorem sum_two_squares_div_sum_two_squaresℚ
    {α β : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hα₂ : IsSumTwoSquaresℚ α) (hβ₂ : IsSumTwoSquaresℚ β) :
    IsSumTwoSquaresℚ (α / β) := by
  obtain ⟨a, b, rfl⟩ := hα₂
  obtain ⟨c, d, hcd⟩ := hβ₂
  refine ⟨(a * c - b * d) / β, (a * d + b * c) / β, ?_⟩
  rw [div_pow, div_pow, ← add_div, ← sq_add_sq_mul_sq_add_sq, ← hcd, sq β,
    mul_div_mul_right _ _ hβ]

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

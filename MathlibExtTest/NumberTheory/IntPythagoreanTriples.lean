/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IntPythagoreanTriples

/-! # Tests for Amato's product of integral Pythagorean triples -/

open MetaMathlibExt

-- Two nonzero signed triples can multiply to zero.
example : pythagoreanTripleMul ((0, 1, 1) : ℤ × ℤ × ℤ) (0, -1, 1) = (0, 0, 0) := by
  decide

-- Nonnegative closure also applies to triples with zero first coordinate.
example (n : ℕ) :
    let p := pythagoreanTripleMul ((0, n, n) : ℤ × ℤ × ℤ) (3, 4, 5)
    p.1 ^ 2 + p.2.1 ^ 2 = p.2.2 ^ 2 ∧ 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 := by
  apply intPythagoreanTriples_commMonoid.2.2.1 (0, n, n) _ (3, 4, 5) _
  · exact ⟨by simp, le_rfl, Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  · decide

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.BigOperators.AffineEmod

/-!
# Tests for reindexing by an affine map modulo `n`
-/

namespace MathlibExtTest.AffineEmod

/-- `b ↦ (1 + 2 b) mod 5` permutes `{0, …, 4}`. -/
example (f : ℤ → ℕ) :
    ∑ b ∈ Finset.range 5, f ((1 + 2 * b) % (5 : ℕ)) = ∑ c ∈ Finset.range 5, f c :=
  Finset.sum_range_add_mul_emod (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) 1 f

/-- A negative multiplier: `b ↦ -b mod 4` permutes `{1, 2, 3}`. -/
example (f : ℤ → ℕ) :
    ∑ b ∈ Finset.Icc 1 (4 - 1), f (-1 * (b : ℕ) % (4 : ℕ)) =
      ∑ c ∈ Finset.Icc 1 (4 - 1), f (c : ℕ) :=
  Finset.sum_Icc_mul_emod (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) f

/-- Concretely, for `f = id` and `α = 3`, `n = 4`: `3 + 2 + 1 = 1 + 2 + 3`. -/
example : ∑ b ∈ Finset.Icc 1 (4 - 1), (3 * ((b : ℕ) : ℤ) % (4 : ℕ)) = 6 := by
  rw [Finset.sum_Icc_mul_emod (f := fun x : ℤ => x) (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)]
  decide

/-- Coprimality is needed: `b ↦ 2 b mod 4` sends `{1, 2, 3}` to `{2, 0, 2}`. -/
example : ∑ b ∈ Finset.Icc 1 (4 - 1), (2 * ((b : ℕ) : ℤ) % (4 : ℕ)) ≠
    ∑ c ∈ Finset.Icc 1 (4 - 1), ((c : ℕ) : ℤ) := by
  decide

end MathlibExtTest.AffineEmod

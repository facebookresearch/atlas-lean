/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.BigOperators.HomogeneousGeomSum

/-!
# Boundary cases for the product formula for homogeneous sums
-/

open MetaMathlibExt

-- The degree-zero factor leaves all n + 1 unit summands.
example (n : ℕ) :
    ∑ j ∈ Finset.range (0 + n + 1), (1 : ℤ) ^ j * 1 ^ (0 + n - j) = (n : ℤ) + 1 := by
  rw [sum_pow_mul_pow_add_eq]
  simp

-- With coincident bases the correction can still be nonzero.
example {R : Type*} [CommRing R] (a : R) :
    ∑ j ∈ Finset.range 3, a ^ j * a ^ (2 - j) = (a + a) * (a + a) - a * a := by
  simpa [Finset.sum_range_succ] using sum_pow_mul_pow_add_eq a a 1 1

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomicProduct

/-! # Tests for the homogenized cyclotomic product -/

open MetaMathlibExt

-- With second argument zero, the product retains the full power of the first argument.
example {n : ℕ} (hn : 0 < n) (a : ℤ) :
    ∏ d ∈ n.divisors, homogenizedCyclotomic d a 0 = a ^ n := by
  simpa [zero_pow hn.ne'] using prod_divisors_homogenizedCyclotomic hn a 0

-- The ratio of the arguments can be negative and nonintegral, even for a composite index.
example : ∏ d ∈ (9 : ℕ).divisors, homogenizedCyclotomic d 2 (-3) = 20195 := by
  rw [prod_divisors_homogenizedCyclotomic (by decide)]
  norm_num

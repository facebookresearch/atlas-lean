/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyNumeratorPrimePow

open MathlibExt.NumberTheory.FareyNumeratorWanted

-- The lower endpoint does not contribute when the numerator is a prime power.
example : (fareyNumeratorCount 9 (3 ^ 2) : ℤ) = 0 := by
  rw [fareyNumeratorCount_prime_pow 3 2 9 (by decide) (by decide) (by decide)]
  decide +kernel

-- Of 9 through 16, the admissible denominators are 10, 11, 13, 14 and 16.
example : (fareyNumeratorCount 16 (3 ^ 2) : ℤ) = 5 := by
  rw [fareyNumeratorCount_prime_pow 3 2 16 (by decide) (by decide) (by decide)]
  decide +kernel

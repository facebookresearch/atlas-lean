/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WalkingToInfinity

open MetaMathlibExt

-- The smallest admissible pair gives 4 - 1 = 3.
example : ¬ ∃ m : ℕ, 3 = 2 ^ m :=
  two_pow_sub_succ_ne_two_pow 0 2 (by decide)

-- For p + 1 = 5 the ceiling logarithm rounds up, and k = 5 gives 32 - 5 = 27.
example : ¬ ∃ m : ℕ, 27 = 2 ^ m :=
  two_pow_sub_succ_ne_two_pow 4 5 (by decide)

-- One exponent below the bound, subtracting a power of two can give it back.
example (r : ℕ) : 2 ^ (r + 1) - 2 ^ r = 2 ^ r := by
  rw [Nat.pow_succ]
  omega

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TribonacciEveryThirdTerm

namespace MetaMathlibExt.TribonacciEveryThirdTermTest

private def a077943 : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => 2 * a077943 (n + 2) - 2 * a077943 (n + 1) + 2 * a077943 n

-- The first sampled index is three.
example : a077943 3 = 2 :=
  (two_pow_mul_tribonacci_eq a077943 rfl rfl rfl a077943.eq_4 0).symm

-- The first term beyond the three base cases uses the subsequence recurrence.
example : a077943 12 = 64 :=
  (two_pow_mul_tribonacci_eq a077943 rfl rfl rfl a077943.eq_4 3).symm

end MetaMathlibExt.TribonacciEveryThirdTermTest

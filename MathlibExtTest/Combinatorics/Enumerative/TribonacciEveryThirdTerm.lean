/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TribonacciEveryThirdTerm

namespace MetaMathlibExt.TribonacciEveryThirdTermTest

private def paddedA077943 : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => 2 * paddedA077943 (n + 2) - 2 * paddedA077943 (n + 1) + 2 * paddedA077943 n

-- Padded index 3 is OEIS index 1, the first sampled term.
example : paddedA077943 3 = 2 :=
  (two_pow_mul_tribonacci_eq paddedA077943 rfl rfl rfl paddedA077943.eq_4 0).symm

-- Padded index 12 is OEIS index 10, the first sample beyond the three base cases.
example : paddedA077943 12 = 64 :=
  (two_pow_mul_tribonacci_eq paddedA077943 rfl rfl rfl paddedA077943.eq_4 3).symm

end MetaMathlibExt.TribonacciEveryThirdTermTest

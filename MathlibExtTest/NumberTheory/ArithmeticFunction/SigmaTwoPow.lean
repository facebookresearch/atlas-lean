/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SigmaTwoPow

namespace MetaMathlibExt

-- Check the divisor sums for the zeroth and a positive power independently of the formula.
example : ArithmeticFunction.sigma 1 (2 ^ 0) + 1 = 2 ^ (0 + 1) := by decide

example : ArithmeticFunction.sigma 1 (2 ^ 3) + 1 = 2 ^ (3 + 1) := by decide

-- Exercise the public theorem with just the divisor-sum module imported.
example : ArithmeticFunction.sigma 1 (2 ^ 0) + 1 = 2 ^ (0 + 1) :=
  sigma_two_pow_add_one 0

example : ArithmeticFunction.sigma 1 (2 ^ 3) + 1 = 2 ^ (3 + 1) :=
  sigma_two_pow_add_one 3

end MetaMathlibExt

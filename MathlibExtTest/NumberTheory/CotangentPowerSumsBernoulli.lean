/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CotangentPowerSumsBernoulli

open MetaMathlibExt

-- Each example evaluates the Bernoulli tuple sum on the right-hand side of the
-- theorem at a concrete same-parity index, including the first column and a
-- tuple sum with more than one summand.
example : cotangentPowerCoeff 3 1 = 1 := by
  rw [cotangentPowerCoeff_eq_bernoulli_tuple_sum (by decide) (by decide) (by decide)]
  decide +kernel

example : cotangentPowerCoeff 4 2 = -4 / 3 := by
  rw [cotangentPowerCoeff_eq_bernoulli_tuple_sum (by decide) (by decide) (by decide)]
  decide +kernel

example : cotangentPowerCoeff 5 3 = 5 / 6 := by
  rw [cotangentPowerCoeff_eq_bernoulli_tuple_sum (by decide) (by decide) (by decide)]
  decide +kernel

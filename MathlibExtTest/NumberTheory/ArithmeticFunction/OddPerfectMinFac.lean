/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectMinFac

-- Check the public statement, including the rational division and strict inequality.
example (N : ℕ) (hodd : Odd N) (hperf : N.Perfect) :
    (N.minFac : ℚ) < 3 * N.primeFactors.card / 7 + 3 :=
  MetaMathlibExt.oddPerfect_minFac_lt N hodd hperf

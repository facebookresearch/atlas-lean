/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumRecurrences

open Finset MetaMathlibExt

-- On the diagonal the half-open summation range is empty, even at degree zero.
example (ℓ : ℕ) (x y : ℂ) : alternatingBinomialPowerSum ℓ (ℓ + 1) x y = 0 := by
  simpa using (alternatingBinomialPowerSum_recurrences x y ℓ ℓ).2.2.1

-- At order zero the correction term involving the predecessor drops out.
example (ℓ : ℕ) (x y : ℂ) :
    alternatingBinomialPowerSum (ℓ + 1) 0 x y = y * alternatingBinomialPowerSum ℓ 0 x y := by
  simpa using (alternatingBinomialPowerSum_recurrences x y ℓ 0).2.2.2.1

-- The first difference of a quadratic has constant derivative in the shift parameter.
example (x y : ℂ) : deriv (fun z => alternatingBinomialPowerSum 2 1 x z) y = -2 * x := by
  rw [(alternatingBinomialPowerSum_recurrences x y 2 1).2.2.2.2.2.1 (by decide)]
  simp [alternatingBinomialPowerSum, sum_range_succ]

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CarlitzSumDerivAndRecurrence

open Finset MetaMathlibExt

-- At n = -1 the shift is zero, so the cubic's first difference has derivative -3.
example : deriv (fun z : ℂ => alternatingBinomialPowerSum 3 1 1 (z + 1)) (-1) = -3 := by
  rw [(carlitzSum_deriv_and_recurrence (ℓ := 3) (m := 1) (by decide) (by decide) (-1)).1]
  norm_num [alternatingBinomialPowerSum, sum_range_succ]

-- At the least allowed degree and order, the recurrence uses the order-zero sum.
example (n : ℂ) : alternatingBinomialPowerSum 1 1 1 (n + 1) = -1 := by
  rw [(carlitzSum_deriv_and_recurrence (ℓ := 1) (m := 1) (by decide) (by decide) n).2]
  simp [alternatingBinomialPowerSum, sum_range_succ]

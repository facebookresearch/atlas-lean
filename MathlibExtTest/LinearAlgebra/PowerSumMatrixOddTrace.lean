/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.PowerSumMatrixOddTrace
import Mathlib.Tactic.NormNum

namespace MathlibExt.LinearAlgebra.PowerSumMatrixWanted

-- When n = 1 there are no pairs.
example (k : ℕ) : ∑ i ∈ Finset.Icc (1 : ℕ) 1, (i : ℝ) ^ k = 1 := by
  simpa only [show Finset.Icc (1 : ℕ) (1 / 2) = ∅ by decide, Finset.sum_empty, zero_add,
    Nat.cast_one, one_pow] using sum_pow_eq_sum_trace_add_of_odd 1 k (by decide)

-- At k = 0 each pair contributes 2, in addition to the last term.
example : ∑ i ∈ Finset.Icc (1 : ℕ) 3, (i : ℝ) ^ (0 : ℕ) = 3 := by
  have h := sum_pow_eq_sum_trace_add_of_odd 3 0 (by decide)
  rw [show (3 : ℕ) / 2 = 1 by decide, Finset.Icc_self, Finset.sum_singleton,
    pow_zero, Matrix.trace_one, pow_zero] at h
  convert h using 1
  norm_num [Fintype.card_fin]

end MathlibExt.LinearAlgebra.PowerSumMatrixWanted

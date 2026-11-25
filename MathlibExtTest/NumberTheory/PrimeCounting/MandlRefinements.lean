/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.MandlRefinements
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

/-!
# Endpoint test for the auxiliary logarithmic inequality
-/

namespace MetaMathlibExt

-- At the least admissible index, the iterated logarithm is negative.
example :
    let L := Real.log 2
    Real.log L < 0 ∧
      4.151332 * (Real.log L - 2) / L + 3.151332 * (Real.log L - 1) / L +
        3.151332 * (Real.log L - 2) / L ^ 2 ≤ 1 := by
  refine ⟨Real.log_neg (Real.log_pos (by norm_num)) ?_, ?_⟩
  · linarith only [Real.log_two_lt_d9]
  · simpa using loglog_ratio_sum_le_one 2 le_rfl

end MetaMathlibExt

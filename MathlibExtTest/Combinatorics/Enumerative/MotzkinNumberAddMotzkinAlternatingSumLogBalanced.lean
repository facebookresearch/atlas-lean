/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MotzkinNumberAddMotzkinAlternatingSumLogBalanced

namespace MetaMathlibExt.motzkinNumber_add_motzkinAlternatingSum_logBalanced

private abbrev sumAt (n : ℕ) : ℤ := (motzkinNumber n : ℤ) + motzkinAlternatingSum n

-- The summed sequence begins 2, 1, 4, 6, 16, 35, 88.
example : sumAt 6 = 88 := by
  simp only [sumAt, motzkinAlternatingSum, motzkinNumber_eq_sum_range_half,
    catalan_eq_centralBinom_div]
  decide

-- The log-convexity inequality fails immediately before the cutoff.
example : sumAt 5 * sumAt 7 < sumAt 6 ^ 2 := by
  simp only [sumAt, motzkinAlternatingSum, motzkinNumber_eq_sum_range_half,
    catalan_eq_centralBinom_div]
  decide

example : sumAt 7 ^ 2 ≤ sumAt 6 * sumAt 8 ∧
    7 * (sumAt 6 * sumAt 8) ≤ 8 * sumAt 7 ^ 2 :=
  motzkinNumber_add_motzkinAlternatingSum_logBalanced 7 (by decide)

example : sumAt 10 ^ 2 ≤ sumAt 9 * sumAt 11 ∧
    10 * (sumAt 9 * sumAt 11) ≤ 11 * sumAt 10 ^ 2 :=
  motzkinNumber_add_motzkinAlternatingSum_logBalanced 10 (by decide)

end MetaMathlibExt.motzkinNumber_add_motzkinAlternatingSum_logBalanced

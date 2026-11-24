/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MotzkinAlternatingSumProducts

namespace MetaMathlibExt.motzkinAlternatingSum_mul_succ_logConvex_logBalanced

private abbrev productAt (n : ℕ) := motzkinAlternatingSum n * motzkinAlternatingSum (n + 1)

-- The log-convexity inequality fails immediately before the cutoff.
example : productAt 5 * productAt 7 < productAt 6 ^ 2 := by
  simp only [productAt, motzkinAlternatingSum, motzkinNumber_eq_sum_range_half,
    catalan_eq_centralBinom_div]
  decide

example : productAt 7 ^ 2 ≤ productAt 6 * productAt 8 :=
  motzkinAlternatingSum_mul_succ_logConvex_logBalanced.1 7 (by decide)

example : productAt 10 ^ 2 ≤ productAt 9 * productAt 11 ∧
    10 * (productAt 9 * productAt 11) ≤ 11 * productAt 10 ^ 2 :=
  motzkinAlternatingSum_mul_succ_logConvex_logBalanced.2 10 (by decide)

end MetaMathlibExt.motzkinAlternatingSum_mul_succ_logConvex_logBalanced

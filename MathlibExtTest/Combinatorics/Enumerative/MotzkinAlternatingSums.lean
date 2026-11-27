/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MotzkinAlternatingSums

namespace MetaMathlibExt.motzkinAlternatingSum_logBalanced_tempered

-- The log-convexity bound fails one index before its stated cutoff.
example : motzkinAlternatingSum 7 * motzkinAlternatingSum 9 < motzkinAlternatingSum 8 ^ 2 := by
  simp only [motzkinAlternatingSum, motzkinNumber_eq_sum_range_half, catalan_eq_centralBinom_div]
  decide

-- The upper tempered bound also fails one index before its stated cutoff.
example : 6 * motzkinAlternatingSum 5 ^ 2 < 5 * (motzkinAlternatingSum 4 *
    motzkinAlternatingSum 6) := by
  simp only [motzkinAlternatingSum, motzkinNumber_eq_sum_range_half, catalan_eq_centralBinom_div]
  decide

example : motzkinAlternatingSum 9 ^ 2 ≤ motzkinAlternatingSum 8 * motzkinAlternatingSum 10 :=
  (motzkinAlternatingSum_logBalanced_tempered.1 9 (by decide)).1

example : 6 * (motzkinAlternatingSum 5 * motzkinAlternatingSum 7) ≤
    7 * motzkinAlternatingSum 6 ^ 2 :=
  (motzkinAlternatingSum_logBalanced_tempered.2 6 (by decide)).2

end MetaMathlibExt.motzkinAlternatingSum_logBalanced_tempered

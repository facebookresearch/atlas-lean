/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.SigmoidLogOdds

/-!
# Tests for `Real.sigmoid_log_sub_log`

Odds `3 : 1` give probability `3/4`.
-/

namespace MathlibExtTest.SigmoidLogOdds

example : Real.sigmoid (Real.log 3 - Real.log 1) = 3 / 4 := by
  rw [Real.sigmoid_log_sub_log (by norm_num) (by norm_num)]
  norm_num

end MathlibExtTest.SigmoidLogOdds

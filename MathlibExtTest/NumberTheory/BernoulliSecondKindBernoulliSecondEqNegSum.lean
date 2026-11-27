/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BernoulliSecondKindBernoulliSecondEqNegSum

open MathlibExt.NumberTheory.BernoulliSecondKindWanted MetaMathlibExt

namespace MathlibExtTest.NumberTheory.BernoulliSecondKindBernoulliSecondEqNegSum

-- At index one the sum has a single term.
example : bernoulliSecond 1 = 1 / 2 := by
  have h := bernoulliSecond_eq_neg_sum 1 (by decide)
  norm_num at h
  linarith

-- At index two the vanishing Stirling term leaves a single contribution.
example : bernoulliSecond 2 = -1 / 6 := by
  have h := bernoulliSecond_eq_neg_sum 2 (by decide)
  rw [show Finset.Icc 1 2 = {1, 2} by decide] at h
  norm_num at h
  linarith

end MathlibExtTest.NumberTheory.BernoulliSecondKindBernoulliSecondEqNegSum

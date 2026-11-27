/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKindStirling

open MathlibExt.NumberTheory.BernoulliSecondKindWanted MetaMathlibExt

-- The lower endpoint fixes the sign convention for the two Bernoulli sequences.
example : bernoulliSecond 1 = 1 / 2 := by
  have h := bernoulli_eq_neg_sum 1 (by decide)
  norm_num at h
  linarith

-- At index three, the two nonzero Stirling terms cancel.
example : 3 / 2 * bernoulliSecond 2 + bernoulliSecond 3 = 0 := by
  have h := bernoulli_eq_neg_sum 3 (by decide)
  rw [bernoulli_eq_zero_of_odd (by decide) (by decide)] at h
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide] at h
  norm_num [Nat.stirlingSecond] at h
  linarith

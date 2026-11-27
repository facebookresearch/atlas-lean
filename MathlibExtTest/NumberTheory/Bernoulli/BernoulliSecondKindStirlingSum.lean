/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKindStirlingSum
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.BernoulliSecondKindWanted MetaMathlibExt

-- The constant term comes entirely from the term indexed by zero.
example : bernoulliSecond 0 = 1 := by
  rw [bernoulliSecond_eq_sum]
  simp

-- The two nonzero signed Stirling terms at n = 2 subtract rather than add.
example : bernoulliSecond 2 = -1 / 6 := by
  rw [bernoulliSecond_eq_sum]
  norm_num [Finset.sum_range_succ, signedStirlingFirst_succ_succ]

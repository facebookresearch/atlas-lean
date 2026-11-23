/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DoublyExponentialReciprocalSum

open MetaMathlibExt

-- At r = 2, the initial nearest-integer choice is a tie and rounds up.
example : pseudoGreedyGap 2 0 = -(1 / 2 : ℝ) := by
  norm_num [pseudoGreedyGap, pseudoGreedyExpansion, pseudoGreedyRemainder, Int.floor_eq_iff]

-- For r = 3, the first denominator is one and the next remainder is two.
example : pseudoGreedyRemainder 3 1 = 2 := by
  norm_num [pseudoGreedyRemainder, Int.floor_eq_iff]

example : HasSum (fun n => 1 / (pseudoGreedyExpansion 3 n : ℝ)) 3 :=
  hasSum_one_div_pseudoGreedyExpansion (by norm_num)

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Dilog

open Real

example : li2 0 = 0 := li2_zero

example : li2 1 = π ^ 2 / 6 := li2_one

example : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2)
    (li2 (1 / 2)) :=
  hasSum_li2 (by norm_num)

example : HasDerivAt li2 (-Real.log (1 - 1 / 2) / (1 / 2)) (1 / 2) :=
  hasDerivAt_li2 (by norm_num) (by norm_num)

example : HasDerivAt li2
    (∑' n : ℕ, (0 : ℝ) ^ n / (((n + 1 : ℕ)) : ℝ)) 0 :=
  hasDerivAt_li2_tsum (by norm_num)

example : ContinuousOn li2 (Set.Icc (-1) 1) := continuousOn_li2

example : ContinuousAt li2 0 := continuousAt_li2_zero

example : li2 (1 / 2) + li2 (1 - 1 / 2) =
    π ^ 2 / 6 - Real.log (1 / 2) * Real.log (1 - 1 / 2) :=
  li2_reflection ⟨by norm_num, by norm_num⟩

#print axioms Real.li2_one
#print axioms Real.li2_reflection

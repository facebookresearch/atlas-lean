/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Dilog

open Real

example : li2PowerSeries 0 = 0 := li2PowerSeries_zero

example : li2PowerSeries 1 = π ^ 2 / 6 := li2PowerSeries_one

example : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) / (((n + 1 : ℕ)) : ℝ) ^ 2)
    (li2PowerSeries (1 / 2)) :=
  hasSum_li2PowerSeries (by norm_num)

example : HasDerivAt li2PowerSeries (-Real.log (1 - 1 / 2) / (1 / 2)) (1 / 2) :=
  hasDerivAt_li2PowerSeries (by norm_num) (by norm_num)

example : HasDerivAt li2PowerSeries
    (∑' n : ℕ, (0 : ℝ) ^ n / (((n + 1 : ℕ)) : ℝ)) 0 :=
  hasDerivAt_li2PowerSeries_tsum (by norm_num)

example : ContinuousOn li2PowerSeries (Set.Icc (-1) 1) := continuousOn_li2PowerSeries

example : ContinuousAt li2PowerSeries 0 := continuousAt_li2PowerSeries_zero

example : li2PowerSeries (1 / 2) + li2PowerSeries (1 - 1 / 2) =
    π ^ 2 / 6 - Real.log (1 / 2) * Real.log (1 - 1 / 2) :=
  li2PowerSeries_reflection ⟨by norm_num, by norm_num⟩

#print axioms Real.li2PowerSeries_one
#print axioms Real.li2PowerSeries_reflection

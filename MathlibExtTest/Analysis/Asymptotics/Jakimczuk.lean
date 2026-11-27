/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Filter.AtTopBot.Archimedean
import MathlibExt.Analysis.Asymptotics.Jakimczuk

open Asymptotics Filter Finset

/-- The sequences can differ at index one, and the comparison sequence can take any value
at zero. -/
example (x : ℝ) :
    (fun n : ℕ => ∑ i ∈ Icc 1 n, if i = 1 then (2 : ℝ) else 1) ~[atTop]
      fun n : ℕ => ∑ i ∈ Icc 1 n, if i = 0 then x else 1 := by
  apply MetaMathlibExt.sum_isEquivalent_of_isEquivalent
    (fun i => if i = 1 then 2 else 1) (fun i => if i = 0 then x else 1)
    (ha := by
      intro i _
      split <;> norm_num)
  · intro i hi
    simp [Nat.ne_of_gt hi]
  · apply EventuallyEq.isEquivalent
    filter_upwards [eventually_gt_atTop 1] with i hi
    simp [hi.ne', (zero_lt_one.trans hi).ne']
  · have hsum (n : ℕ) : (∑ i ∈ Icc 1 n, if i = 0 then x else 1) = n := by
      calc
        _ = ∑ _i ∈ Icc 1 n, (1 : ℝ) := sum_congr rfl fun i hi => by
          simp [Nat.ne_of_gt (mem_Icc.mp hi).1]
        _ = _ := by simp
    simpa only [hsum] using (tendsto_natCast_atTop_atTop (R := ℝ))

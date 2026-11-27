/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SubsetSumConcentrationErdosProblem362

open MathlibExt.Combinatorics.SubsetSumConcentrationErdosProblem362Wanted

-- The same constant must allow both choices of whether to include zero, even for a singleton.
example : ∃ C : ℝ, 1 ≤ C ∧ 4 ≤ C * 2 ^ 4 / (4 : ℝ) ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := subsetSumCountBound_holds
  have hz := hC {0} 0 (by simp)
  have hfour := hC {0, 1, 2, 3} 3 (by simp)
  have count_zero :
      (({0} : Finset ℕ).powerset.filter fun S => ∑ i ∈ S, i = 0).card = 2 := by decide
  have count_three :
      (({0, 1, 2, 3} : Finset ℕ).powerset.filter fun S => ∑ i ∈ S, i = 3).card = 4 := by decide
  rw [count_zero] at hz
  norm_num at hz
  refine ⟨C, by linarith, ?_⟩
  simpa only [count_three, show ({0, 1, 2, 3} : Finset ℕ).card = 4 by decide,
    Nat.cast_ofNat] using hfour

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Monopoly.Lerner
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Monopoly.Lerner`

With demand `10 - q` and cost `2 q`, the optimum `q = 4` has price `6`, elasticity `-3/2` and Lerner
index `2/3`. -/

open MathlibExt.Economics.Monopoly

namespace MathlibExtTest.Economics.Monopoly.Lerner

theorem isLocalMax_linear_example :
    IsLocalMax (fun x : ℝ => x * (10 - x) - 2 * x) 4 := by
  apply Filter.Eventually.of_forall
  intro x
  change x * (10 - x) - 2 * x ≤ 4 * (10 - 4) - 2 * 4
  nlinarith [sq_nonneg (x - 4)]

theorem lerner_linear_example :
    (6 - 2) / (6 : ℝ) = 1 / |priceElasticity (fun x : ℝ => 10 - x) (-1) 4| := by
  have hP : HasDerivAt (fun x : ℝ => 10 - x) (-1) 4 := by
    simpa using ((hasDerivAt_id' (4 : ℝ)).const_sub (10 : ℝ))
  have hC : HasDerivAt (fun x : ℝ => 2 * x) 2 4 := by
    simpa using ((hasDerivAt_id' (4 : ℝ)).const_mul (2 : ℝ))
  have h := lerner_of_isLocalMax hP hC isLocalMax_linear_example (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem priceElasticity_linear_example :
    priceElasticity (fun x : ℝ => 10 - x) (-1) 4 = -3 / 2 := by
  unfold priceElasticity
  norm_num

theorem lernerIndex_linear_example : (6 - 2) / (6 : ℝ) = 2 / 3 := by
  norm_num

theorem lernerValue_linear_example :
    1 / |priceElasticity (fun x : ℝ => 10 - x) (-1) 4| = (2 : ℝ) / 3 := by
  rw [priceElasticity_linear_example]
  norm_num

end MathlibExtTest.Economics.Monopoly.Lerner

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.ContinuousMultiplicativeFunctionalEqExp

open MathlibExt.Analysis.SpecialFunctions.ContinuousMultiplicativeFunctionalEqExpWanted

-- A single zero forces the whole solution to vanish.
example {f : ℝ → ℝ} (hadd : ∀ x y : ℝ, f x * f y = f (x + y))
    (hcont : Continuous f) {a : ℝ} (ha : f a = 0) : f = 0 := by
  by_contra hnz
  obtain ⟨c, hc⟩ := exists_eq_exp_mul_of_map_add_eq_mul hadd hcont hnz
  exact Real.exp_ne_zero _ ((hc a).symm.trans ha)

-- A solution with value one at one has exponent zero and is constant.
example {f : ℝ → ℝ} (hadd : ∀ x y : ℝ, f x * f y = f (x + y))
    (hcont : Continuous f) (hone : f 1 = 1) : f = 1 := by
  have hnz : f ≠ 0 := by
    intro h
    simp [h] at hone
  obtain ⟨c, hc⟩ := exists_eq_exp_mul_of_map_add_eq_mul hadd hcont hnz
  have hc0 : c = 0 := by simpa [hone] using (hc 1).symm
  funext x
  simpa [hc0] using hc x

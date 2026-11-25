/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.BeurlingAhlforsL2

open MathlibExt.Analysis.BeurlingAhlfors MathlibExt.Analysis.BeurlingAhlforsWanted

-- The computed infimum rules out the empty set of admissible constants.
example : Set.Nonempty {C : ℝ | 0 ≤ C ∧ IsBound 2 C} := by
  by_contra h
  have hempty := Set.not_nonempty_iff_eq_empty.mp h
  simpa [beurlingNorm, hempty] using l2Norm_wanted

-- Every nonnegative constant below one fails the bound, including zero.
example {C : ℝ} (hC : 0 ≤ C) (hlt : C < 1) : ¬IsBound 2 C := by
  intro h
  have hl := beurlingNorm_le_of_isBound hC h
  rw [l2Norm_wanted] at hl
  exact (not_le_of_gt hlt) hl

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Beatty.GeneralizedWythoff

open MetaMathlibExt
open scoped goldenRatio

-- Both compositions at the first index, with a negative linear coefficient and a nonzero shift.
example : generalizedBeatty 3 (-2) 5 ⌊(1 : ℝ) * φ⌋₊ = 6 ∧
    generalizedBeatty 3 (-2) 5 (⌊(1 : ℝ) * φ⌋₊ + 1) = 10 := by
  have h := generalizedBeatty_comp_wythoff 3 (-2) 5 1 (by decide)
  norm_num [generalizedBeatty_one] at h ⊢
  exact h

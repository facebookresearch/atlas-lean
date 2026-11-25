/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CotangentLimit

open Real Filter Topology

-- At x = -π the predecessor angle hits a pole at k = 2, yet the limit is negative.
example : sin (-π / ((2 : ℝ) - 1)) = 0 := by norm_num

example : Tendsto (fun k : ℕ => (1 / (k : ℝ) - 1) * cot (-π / (k - 1)) +
    (1 / (k : ℝ) + 1) * cot (-π / (k + 1))) atTop (𝓝 (-(4 / π))) := by
  simpa only [div_neg] using
    MetaMathlibExt.tendsto_cot_div_pred_add_cot_div_succ (x := -π) (neg_ne_zero.mpr pi_ne_zero)

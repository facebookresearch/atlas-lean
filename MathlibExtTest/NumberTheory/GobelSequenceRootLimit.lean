/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelSequenceRootLimit

open Filter Topology MetaMathlibExt

-- The original Göbel sequence, at the lower endpoint of both parameters.
example : ∃ C : ℝ, 1 < C ∧
    Tendsto (fun n : ℕ => (gobelSequence 2 2 n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 C) :=
  gobelSequence_root_tendsto_gt_one 2 2 le_rfl le_rfl

-- Different parameters: only the recurrence exponent governs the normalization.
example : ∃ C : ℝ, 1 < C ∧
    Tendsto (fun n : ℕ => (gobelSequence 3 5 n : ℝ) ^ ((1 : ℝ) / (3 : ℝ) ^ n)) atTop (𝓝 C) :=
  gobelSequence_root_tendsto_gt_one 3 5 (by decide) (by decide)

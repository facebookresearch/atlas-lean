/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquarefreeOneModEight

/-! # Tests for the relative density of square-free integers congruent to one modulo eight -/

open Finset Filter Topology

-- Both counts include the square-free unit. The numerator skips 9 and includes the endpoint 17.
example : ((Icc 1 17).filter (fun t : ℕ => Squarefree t ∧ t % 8 = 1)) = {1, 17} := by
  decide +kernel

example : ((Icc 1 17).filter Squarefree).card = 12 := by decide +kernel

-- The limit applies to the ratio with the upper endpoint included in both counts.
example : Tendsto (fun X : ℕ =>
    (((Icc 1 X).filter (fun t => Squarefree t ∧ t % 8 = 1)).card : ℝ) /
      ((Icc 1 X).filter Squarefree).card) atTop (𝓝 (1 / 6)) :=
  MetaMathlibExt.squarefree_one_mod_eight_relativeDensity

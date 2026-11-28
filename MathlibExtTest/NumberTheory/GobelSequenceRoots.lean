/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelSequenceRoots
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The first comparison for the original Göbel sequence is between the roots of 2 and 3.
example : (3 : ℝ) ^ (1 / 4 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) ∧ 1 < (3 : ℝ) ^ (1 / 4 : ℝ) := by
  convert gobelSequence_root_strictAnti 2 2 1 le_rfl le_rfl le_rfl using 1 <;>
    norm_num [gobelSequence]

-- Starting at one instead would make the first two normalized roots equal.
example : (gobelSequence 2 1 2 : ℝ) ^ (1 / 4 : ℝ) =
    (gobelSequence 2 1 1 : ℝ) ^ (1 / 2 : ℝ) := by
  norm_num [gobelSequence]

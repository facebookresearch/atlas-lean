/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LinearChordBubbles
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The nested diagram on four vertices has a single short chord in the middle.
-- Its two bubbles are singletons at the opposite ends of the line.
example : IsLinearChordDiagram 2 Fin.rev ∧ IsBubble (n := 2) Fin.rev 0 1 ∧
    IsBubble (n := 2) Fin.rev 3 1 ∧ ¬IsBubble (n := 2) Fin.rev 0 2 := by decide

example : bubbleCount 0 0 = 0 ∧ bubbleCount 2 0 = 0 := by decide +kernel

-- Six vertices give a nonintegral mean, testing the rational division.
example : (∑ p ∈ Finset.Icc 1 (6 : ℕ), (p : ℚ) * bubbleCount 3 p) /
    (∑ p ∈ Finset.Icc 1 (6 : ℕ), (bubbleCount 3 p : ℚ)) = 20 / 7 := by
  convert mean_bubble_size 3 (by decide) using 1
  norm_num

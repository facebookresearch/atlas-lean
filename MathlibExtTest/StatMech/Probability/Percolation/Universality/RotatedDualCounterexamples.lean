/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.RotatedDualCounterexamples
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.RotatedDualCounterexamples`

* The refutations: the same-box dichotomy with the rotated dual is false
  (`bcc_dichotomy_false`, witness `bcc_wallCfg`: `bcc_wall_noH_noV`), and the hypothesis of
  `dcw_square_dichotomy` is false for `n = 2` and `n = 5` (`bcc_square_dichotomy_hyp_false`).
* `bcc_wallCfg` evaluated on a wall edge and a non-wall edge; `bcc_dualVert_botCfg`;
  `bcc_dualReach_separates` for the wall configuration.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box StatMech.Universality SimpleGraph

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.RotatedDualCounterexamples

example : bcc_wallCfg s(![0, 1], ![1, 1]) = false := (bcc_wallCfg_false_iff _).2 (Or.inr (Or.inl rfl))

example : bcc_wallCfg s(![1, 0], ![2, 0]) = true := by
  decide

example : ¬ ((horizontalCrossingEvent 0 2 0 2)ᶜ ⊆ dualVerticalCrossingEvent 0 2 0 2) :=
  bcc_dichotomy_false

example : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_wall_noH_noV

example : ¬ ∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 5 0 5 → dcw_BarrierRoute ω 5 :=
  bcc_square_dichotomy_hyp_false 5 (by norm_num)

example : DualVerticalCrossing bcc_botCfg 0 2 0 2 := bcc_dualVert_botCfg

example : ¬ (latticeMinusBarrier (bcc_dualBottomReach bcc_wallCfg 2)).Reachable ![0, 0] ![0, 2] :=
  bcc_dualReach_separates _ 2 bcc_noV_wall (by simp [bottomSide]) (by simp [topSide])

end MathlibExtTest.StatMech.Probability.Percolation.Universality.RotatedDualCounterexamples

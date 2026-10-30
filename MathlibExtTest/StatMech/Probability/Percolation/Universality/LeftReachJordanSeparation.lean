/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.LeftReachJordanSeparation
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.LeftReachJordanSeparation`

* For the wall configuration on `rect 0 2 0 2`: the left-reach set separates the sides
  (`jex_wall_separates`) and has a face-boundary cycle (`jex_wall_dualCircuit`).
* `jex_edgeBoundary_nonempty` for the wall configuration, row `c = 1`.
* `jex_exhaustivity_of_barrier` instantiated with the all-closed configuration on `rect 0 2 0 2`
  (no horizontal crossing, `pdc_allClosed_noH`; a rotated-dual vertical crossing,
  `bcc_dualVert_botCfg`). The theorem is trivial (`Or.inr`), as its docstring says.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box StatMech.Universality SimpleGraph

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.LeftReachJordanSeparation

example : ¬ (latticeMinusBarrier (bcd_leftReach bcc_wallCfg 2)).Reachable ![0, 1] ![2, 1] :=
  jex_wall_separates (by simp [leftSide]) (by simp [rightSide])

example : ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach bcc_wallCfg 2)).Walk u u),
    cyc.IsCycle := jex_wall_dualCircuit

example : (edgeBoundary 2 (bcd_leftReach bcc_wallCfg 2)).Nonempty :=
  jex_edgeBoundary_nonempty bcc_wallCfg (by norm_num) bcc_noH_wall (c := 1) (by norm_num) (by norm_num)

example : HorizontalCrossing bcc_botCfg 0 2 0 2 ∨ DualVerticalCrossing bcc_botCfg 0 2 0 2 :=
  jex_exhaustivity_of_barrier bcc_botCfg 2 (pdc_allClosed_noH 2 (by norm_num)) bcc_dualVert_botCfg

end MathlibExtTest.StatMech.Probability.Percolation.Universality.LeftReachJordanSeparation

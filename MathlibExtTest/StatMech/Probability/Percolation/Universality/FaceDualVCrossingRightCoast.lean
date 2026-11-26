/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingRightCoast

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingRightCoast`

* `bac_RCoastConnected` holds for the wall configuration; `bac_faceDualVCrossing_of_rCoastConnected`
  is instantiated there.
* `bac_rightWall_mem_rightComplement` and `bac_gap_mem_rightComplement` at small sites.
* `bac_wall_leftReach_iff`: the left cluster of the wall configuration is column `0`.
-/

@[expose] public section

open StatMech StatMech.Universality StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingRightCoast

example : bac_RCoastConnected bcc_wallCfg 2 := bac_wall_rCoastConnected

example : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  bac_faceDualVCrossing_of_rCoastConnected bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    bac_wall_rCoastConnected

example : (![2, 1] : Site 2) ∈ bac_rightComplement bcc_wallCfg 2 :=
  bac_rightWall_mem_rightComplement bcc_wallCfg 2 bcc_noH_wall (by norm_num) (by norm_num)

example : (![1, 0] : Site 2) ∈ bac_rightComplement bcc_wallCfg 2 := by
  simpa using bac_gap_mem_rightComplement bcc_wallCfg 2 bcc_noH_wall (c := 0) (r := 0)
    le_rfl (by norm_num) (mbc_wall_rightFrontier_at le_rfl (by norm_num))

example : (![0, 2] : Site 2) ∈ bcd_leftReach bcc_wallCfg 2 :=
  (bac_wall_leftReach_iff (by simp [mem_rect])).mpr rfl

end MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingRightCoast

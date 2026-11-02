/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingFrontier

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingFrontier`

* `mbc_exists_rightFrontier` and `mbc_faceDualVCrossing_of_residue` instantiated with the wall
  configuration, whose residual `mbc_FrontierRungsConnect` holds (`mbc_wall_frontierRungsConnect`).
* The right frontier of every row of the wall configuration is column `0`.
-/

@[expose] public section

open StatMech StatMech.Universality StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingFrontier

example : ∃ c : ℤ, mbc_IsRightFrontier bcc_wallCfg 2 c 1 :=
  mbc_exists_rightFrontier bcc_wallCfg 2 (by norm_num) bcc_noH_wall (by norm_num) (by norm_num)

example : mbc_IsRightFrontier bcc_wallCfg 2 0 1 :=
  mbc_wall_rightFrontier_at (by norm_num) (by norm_num)

example : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  mbc_faceDualVCrossing_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    mbc_wall_frontierRungsConnect

end MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingFrontier

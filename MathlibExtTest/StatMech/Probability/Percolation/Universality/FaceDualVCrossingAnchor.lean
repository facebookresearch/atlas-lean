/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingAnchor

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingAnchor`

* `ccc_FrontierReachesBottom` holds for the wall configuration; the equivalence with
  `mbc_FrontierRungsConnect` and `ccc_faceDualVCrossing_of_reachesBottom` are instantiated there.
-/

@[expose] public section

open StatMech StatMech.Universality StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingAnchor

example : ccc_FrontierReachesBottom bcc_wallCfg 2 := ccc_wall_frontierReachesBottom

example : mbc_FrontierRungsConnect bcc_wallCfg 2 :=
  ccc_frontierRungsConnect_of_reachesBottom bcc_wallCfg 2 ccc_wall_frontierReachesBottom

example : ccc_FrontierReachesBottom bcc_wallCfg 2 :=
  ccc_reachesAnchor_of_frontierRungsConnect bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    mbc_wall_frontierRungsConnect

example : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  ccc_faceDualVCrossing_of_reachesBottom bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    ccc_wall_frontierReachesBottom

end MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingAnchor

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingArc

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingArc`

* `crc2_FrontierArcReaches` holds for the wall configuration; `crc2_faceDualVCrossing_of_arc`
  and `crc2_exhaustivity_of_arc` are instantiated there.
-/

@[expose] public section

open StatMech StatMech.Universality StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingArc

example : crc2_FrontierArcReaches bcc_wallCfg 2 := crc2_wall_frontierArcReaches

example : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  crc2_faceDualVCrossing_of_arc bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    crc2_wall_frontierArcReaches

example : HorizontalCrossing bcc_wallCfg 0 2 0 2 ∨ pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  crc2_exhaustivity_of_arc bcc_wallCfg 2 (by norm_num) bcc_noH_wall crc2_wall_frontierArcReaches

end MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingArc

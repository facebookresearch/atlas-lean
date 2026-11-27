/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingPinnedAnchor

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingPinnedAnchor`

* `cac_FrontierReachesBottomAtAnchor` holds for the wall configuration; `cac_atom_of_pinned` and
  `cac_pinned_of_atom` are instantiated there.
-/

@[expose] public section

open StatMech StatMech.Universality StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingPinnedAnchor

example : cac_FrontierReachesBottomAtAnchor bcc_wallCfg 2 := cac_wall_frontierReachesBottomAtAnchor

example : ccc_FrontierReachesBottom bcc_wallCfg 2 :=
  cac_atom_of_pinned bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    cac_wall_frontierReachesBottomAtAnchor

example : pmd_boxFaceBarrier bcc_wallCfg 2 ≤ faceBoundaryGraph (bcd_leftReach bcc_wallCfg 2) :=
  cac_boxFaceBarrier_le_faceBoundaryGraph bcc_wallCfg 2

end MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingPinnedAnchor

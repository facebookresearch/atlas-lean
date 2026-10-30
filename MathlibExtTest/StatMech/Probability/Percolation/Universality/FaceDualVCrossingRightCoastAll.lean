/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingRightCoastAll

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossingRightCoastAll`

* `rcm_RCoastConnectedAll` holds for the wall configuration; `rcm_faceDualVCrossing_of_all` is
  instantiated there.
* `rcm_rightComplement_connected_pair` for the right-complement sites `(1, 0)` and `(2, 0)`.
-/

@[expose] public section

open StatMech StatMech.Universality StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingRightCoastAll

example : rcm_RCoastConnectedAll bcc_wallCfg 2 := rcm_wall_RCoastConnectedAll

example : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  rcm_faceDualVCrossing_of_all bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    rcm_wall_RCoastConnectedAll

example : ∃ (huc : (![1, 0] : Site 2) ∈ bac_boxMinusL bcc_wallCfg 2)
    (hvc : (![2, 0] : Site 2) ∈ bac_boxMinusL bcc_wallCfg 2),
    ((hypercubicLattice 2).induce (bac_boxMinusL bcc_wallCfg 2)).Reachable
      ⟨![1, 0], huc⟩ ⟨![2, 0], hvc⟩ := by
  have hg : (![1, 0] : Site 2) ∈ bac_rightComplement bcc_wallCfg 2 := by
    simpa using bac_gap_mem_rightComplement bcc_wallCfg 2 bcc_noH_wall (c := 0) (r := 0)
      le_rfl (by norm_num) (mbc_wall_rightFrontier_at le_rfl (by norm_num))
  exact rcm_rightComplement_connected_pair bcc_wallCfg 2 bcc_noH_wall hg
    (bac_rightWall_mem_rightComplement bcc_wallCfg 2 bcc_noH_wall (by norm_num) (by norm_num))

end MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossingRightCoastAll

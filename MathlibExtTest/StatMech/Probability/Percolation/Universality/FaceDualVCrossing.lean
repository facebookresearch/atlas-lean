/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.FaceDualVCrossing

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.FaceDualVCrossing`

* `pmd_faceDualVCrossing_of_residue` instantiated with the wall configuration, whose residual
  hypothesis `pmd_BarrierConnectsRows` holds (`pmd_wall_barrierConnectsRows`).
* `pmd_wall_only_face_frame_works`: the face-dual crossing holds while both vertex-frame events
  fail.
* `pmd_boxFaceBarrier_le_faceOpenDual` and `pmd_exhaustivity_of_residue` on the wall configuration.
-/

@[expose] public section

open StatMech StatMech.Universality StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossing

example : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  pmd_faceDualVCrossing_of_residue bcc_wallCfg 2 pmd_wall_barrierConnectsRows

example : HorizontalCrossing bcc_wallCfg 0 2 0 2 ∨ pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  pmd_exhaustivity_of_residue bcc_wallCfg 2 bcc_noH_wall pmd_wall_barrierConnectsRows

example : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 ∧
    ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 ∧ pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  pmd_wall_only_face_frame_works

example : pmd_boxFaceBarrier bcc_wallCfg 2 ≤ fci_faceOpenDual bcc_wallCfg :=
  pmd_boxFaceBarrier_le_faceOpenDual bcc_wallCfg 2

end MathlibExtTest.StatMech.Probability.Percolation.Universality.FaceDualVCrossing

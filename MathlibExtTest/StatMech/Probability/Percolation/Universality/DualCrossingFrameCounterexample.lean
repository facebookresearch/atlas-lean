/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.DualCrossingFrameCounterexample

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.DualCrossingFrameCounterexample`

* `rdv_box_frame_target_false`: the same-box `DualVerticalCrossing` is not implied by the absence
  of a horizontal crossing of `[0, 2]²`.
* `rdv_rotResidue_false_on_noH`: the rotated barrier crossing fails for the wall configuration.
* `rdv_leftReach_wall_x0` at the site `(0, 1)`.
-/

@[expose] public section

open StatMech StatMech.Universality StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.DualCrossingFrameCounterexample

example : ¬ (∀ ω : ConfigSpace (Sym2 (Site 2)),
    ¬ HorizontalCrossing ω 0 2 0 2 → DualVerticalCrossing ω 0 2 0 2) :=
  rdv_box_frame_target_false

example : ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 := rdv_rotResidue_false_on_noH

example : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 ∧
    ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 :=
  rdv_both_targets_false_on_witness

end MathlibExtTest.StatMech.Probability.Percolation.Universality.DualCrossingFrameCounterexample

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Basic

/-!
# Relative-observation gauge invariance

For poses in a group acting on landmarks, the relative
observation `g⁻¹ • l` does not change when every pose and
landmark is transformed by a common group element.
-/

@[expose] public section

namespace Robotics.SLAM

/-- Relative-observation gauge invariance. For poses `g`
in a group `G` acting on landmarks, the relative observation
`g⁻¹ • l` is unchanged when every pose and landmark is
transformed by a common `h`:
`(h * g)⁻¹ • (h • l) = g⁻¹ • l`. -/
theorem relativeObservation_invariant {G : Type*} [Group G]
    {L : Type*} [MulAction G L] (h g : G) (l : L) :
    (h * g)⁻¹ • (h • l) = g⁻¹ • l := by
  rw [mul_inv_rev, mul_smul, inv_smul_smul]

end Robotics.SLAM

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.MoserWormCover.UpperBoundPiOverFour

/-! # Tests for the convex worm cover constant being at most π/4 -/

open MeasureTheory Set
open MoserConvexWormCoverConstant

-- The claim unfolds to the bound on the convex worm cover constant.
example : upperBoundPiOverFour := upperBoundPiOverFour_holds

-- The bound itself, stated directly.
example : convexWormCoverConstant ≤ Real.pi / 4 := upperBoundPiOverFour_holds

-- The disk of diameter one is the convex universal cover whose area gives the bound.
example : IsConvexUniversalCover halfDisk := halfDisk_isConvexUniversalCover

-- Its area is exactly π/4, so the bound is the area of a cover, not a looser estimate.
example : volume halfDisk = ENNReal.ofReal (Real.pi / 4) := halfDisk_volume

-- The constant is also bounded by the area of the closed unit disk, a weaker cover.
example : convexWormCoverConstant ≤ Real.pi := by
  exact upperBoundPiOverFour_holds.trans (by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith [Real.pi_pos])

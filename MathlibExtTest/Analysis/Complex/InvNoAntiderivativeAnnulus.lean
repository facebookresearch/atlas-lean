/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.InvNoAntiderivativeAnnulus

open Metric MathlibExt.Analysis.Complex.InvNoAntiderivativeAnnulusWanted

-- A derivative taken within the open annulus gives the same obstruction.
example : ¬ ∃ F : ℂ → ℂ, ∀ z ∈ ball 0 2 \ closedBall 0 1,
    HasDerivWithinAt F (1 / z) (ball 0 2 \ closedBall 0 1) z := by
  rintro ⟨F, hF⟩
  refine not_exists_hasDerivAt_inv_on_annulus (ball 0 2 \ closedBall 0 1) ?_ ⟨F, ?_⟩
  · ext z
    simp [mem_ball, mem_closedBall, and_comm]
  · intro z hz
    exact (hF z hz).hasDerivAt ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hz)

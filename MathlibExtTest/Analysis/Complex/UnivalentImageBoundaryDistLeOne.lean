/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.UnivalentImageBoundaryDistLeOne

/-! # Sharpness of the boundary distance bound -/

open Metric

namespace MathlibExt.Analysis.Complex.UnivalentImageBoundaryDistLeOneWanted

-- The identity map attains the bound on the unit disc.
example : infDist (0 : ℂ) (frontier (ball (0 : ℂ) 1)) = 1 := by
  apply le_antisymm
  · simpa using infDist_zero_frontier_image_ball_le_one id differentiable_id.differentiableOn
      Function.injective_id.injOn rfl (deriv_id _)
  · rw [frontier_ball _ one_ne_zero, le_infDist (NormedSpace.sphere_nonempty.mpr zero_le_one)]
    intro z hz
    exact (dist_comm (0 : ℂ) z ▸ (mem_sphere.mp hz).ge)

end MathlibExt.Analysis.Complex.UnivalentImageBoundaryDistLeOneWanted

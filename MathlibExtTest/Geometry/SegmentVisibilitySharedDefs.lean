/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.SegmentVisibilitySharedDefs

namespace MathlibExt.Geometry.SegmentVisibilityShared

/-- Two vertices do not make a simple polygon. -/
example (v : Fin 2 → ℝ × ℝ) : ¬ IsSimplePolygon v := fun h => by
  have := h.1
  omega

/-- A repeated consecutive vertex gives a degenerate edge, so no simple polygon. -/
example : ¬ IsSimplePolygon ![((0 : ℝ), (0 : ℝ)), (0, 0), (1, 0)] := fun h =>
  h.2.1 0 rfl

end MathlibExt.Geometry.SegmentVisibilityShared

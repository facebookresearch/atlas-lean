/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Convex.CubeCovering
import MathlibExt.Geometry.Convex.IlluminationInteriorEquivalence

open ConvexCovering

-- A cover of the three-dimensional cube by eight interior translates gives eight directions.
example : IlluminatedByDirections (coordinateCube 3) 8 :=
  (directionalInteriorFormulationsEquivalent 3 (by decide) _
    (coordinateCube_isConvexBody 3) 8).mpr coordinateCube_three_coveredByInteriorTranslates

-- Seven directions would give a cover below the cube's lower bound.
example : ¬ IlluminatedByDirections (coordinateCube 3) 7 := by
  intro h
  have hcover := (directionalInteriorFormulationsEquivalent 3 (by decide) _
    (coordinateCube_isConvexBody 3) 7).mp h
  exact (by decide : ¬ 2 ^ 3 ≤ (7 : ℕ)) (coordinateCube_coveringCount_ge_two_pow hcover)

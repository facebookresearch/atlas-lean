/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.Manifold.RiemannSurfaceGenus

open scoped ContDiff

universe u

-- In particular, two analytic structures on the same underlying surface
-- yield the same genus. No compatibility with the charts is required.
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    [CompactSpace X] [CompactSpace Y] [ConnectedSpace X] [ConnectedSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ω Y] (e : X ≃ₜ Y) :
    RiemannSurface.genus X = RiemannSurface.genus Y := by
  let homology := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) 1).obj
    (ModuleCat.of ℚ (ULift.{u} ℚ))
  let iso := TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e
  exact congrArg (· / 2) (homology.mapIso iso).toLinearEquiv.finrank_eq

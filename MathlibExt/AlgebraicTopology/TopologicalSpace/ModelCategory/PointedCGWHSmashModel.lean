/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.PointedSmash
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHCartesianMonoidalModel
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHPointCofibrant
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure
public import MathlibExt.Topology.Category.PointedCGWH.Closed

/-!
# The smash-model structure on pointed CGWH spaces

The generic closed symmetric monoidal model structure on pointed objects
specializes at the cofibrant terminal CGWH point.  The selected model remains
the sole generic undercategory instance activated by `CGWH.modelCategory`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory HomotopicalAlgebra MonoidalCategory

open scoped CGWH.modelCategory

namespace PointedCGWH.modelCategory

/-- The smash tensor unit of pointed CGWH spaces is cofibrant in the selected
model structure. -/
theorem smashUnit_isCofibrant :
    IsCofibrant (𝟙_ (PointedCGWH.{u, v})) := by
  let _ : IsCofibrant CGWH.point.{u, v} :=
    CGWH.point_isCofibrant
  exact isCofibrant_under_smashUnit
    CGWH.point.{u, v} CGWH.point_isTerminal

end PointedCGWH.modelCategory

namespace CGWH.modelCategory

/-- The sole selected closed symmetric monoidal model structure on pointed
CGWH spaces. -/
noncomputable scoped instance
    instPointedCGWHIsClosedSymmetricMonoidalModelCategory :
    IsClosedSymmetricMonoidalModelCategory PointedCGWH.{u, v} := by
  let _ : IsCofibrant CGWH.point.{u, v} :=
    CGWH.point_isCofibrant
  exact underSmashIsClosedSymmetricMonoidalModelCategory
    CGWH.point.{u, v} CGWH.point_isTerminal

end CGWH.modelCategory

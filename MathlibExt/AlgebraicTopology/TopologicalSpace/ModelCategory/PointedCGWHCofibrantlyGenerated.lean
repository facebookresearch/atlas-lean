/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.UnderCofibrantlyGenerated
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure

/-!
# Cofibrant generation for pointed CGWH spaces

The native CGWH boundary and horn generators are sent through the free
undercategory functor at the named CGWH point.  The reviewed fixed-cardinal
transfer then supplies cofibrant-generation data at the same literal
cardinal.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory MorphismProperty HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH

/-- The realized boundary generators for pointed CGWH spaces. -/
noncomputable def realizedBoundaryInclusions :
    MorphismProperty PointedCGWH.{u, v} :=
  CGWH.realizedBoundaryInclusions.{u, v}.underCostar CGWH.point

/-- The realized horn generators for pointed CGWH spaces. -/
noncomputable def realizedHornInclusions :
    MorphismProperty PointedCGWH.{u, v} :=
  CGWH.realizedHornInclusions.{u, v}.underCostar CGWH.point

/-- Right lifting against pointed boundary generators is detected on the
underlying CGWH map. -/
theorem realizedBoundaryInclusions_rlp :
    realizedBoundaryInclusions.{u, v}.rlp =
      CGWH.realizedBoundaryInclusions.{u, v}.rlp.inverseImage
        pointedToCGWH.{u, v} :=
  MorphismProperty.underCostar_rlp _ _

/-- Right lifting against pointed horn generators is detected on the
underlying CGWH map. -/
theorem realizedHornInclusions_rlp :
    realizedHornInclusions.{u, v}.rlp =
      CGWH.realizedHornInclusions.{u, v}.rlp.inverseImage
        pointedToCGWH.{u, v} :=
  MorphismProperty.underCostar_rlp _ _

/-- Fixed-cardinal cofibrant-generation data for the selected pointed CGWH
model structure. -/
noncomputable def cofibrantGenerationData :
    CofibrantGenerationData PointedCGWH.{u, v}
      realizedGeneratorCardinal.{v} :=
  HomotopicalAlgebra.CofibrantGenerationData.under
    realizedGeneratorCardinal.{v} CGWH.cofibrantGenerationData.{u, v}
      CGWH.point

end PointedCGWH

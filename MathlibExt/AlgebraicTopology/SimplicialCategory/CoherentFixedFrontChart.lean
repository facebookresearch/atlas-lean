/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCubeIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCubeOperators
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeMaximumNaturality

/-!
# Genuine cosimplicial chart of the original realized right Hom

The actual cube identification is natural for all faces and degeneracies.
Both whole inverse maps preserve the same original scalar cells and
structural endpoints. The actual maximum comparison is transported by
this proved chart; its relative frame property remains a separate proof.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontChart
open FixedFrontCubeMap FixedFrontCubeRetraction FixedFrontCubeIso

/-- The genuine entire cosimplicial isomorphism between the constructed original quotient cubes and actual
  realized fixed-front right Homs. -/
def chartIso : RightCubeCosimplicial.diagram.{u} ≅ RightHomCosimplicial.diagram.{u} :=
  NatIso.ofComponents (fun n => cubeIso n.len) (fun θ => FixedFrontCubeOperators.map_naturality θ)

/-- The whole original forward natural transformation is exactly the constructed cosimplicial cube map. -/
theorem chartIso_hom : chartIso.{u}.hom = FixedFrontCubeOperators.chartMap := rfl

/-- Each original chart component retains the actual whole cube isomorphism and both original inverse maps. -/
theorem chartIso_app (n : ℕ) : chartIso.{u}.app ⦋n⦌ = cubeIso n := rfl

/-- Every original inverse chart square commutes on the entire scalar Hom, including all original faces and
  degeneracies. -/
theorem inverse_naturality {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    RightHomResolution.map.{u} θ ≫ readCubeMap m = readCubeMap n ≫ RightCubeCosimplicialMaps.map θ :=
  chartIso.inv.naturality θ

/-- The actual natural maximum map from the original realized fixed-front right Homs to the standard
  cosimplicial simplices. -/
def maximumMap : RightHomCosimplicial.diagram.{u} ⟶ SSet.stdSimplex.{u} :=
  chartIso.inv ≫ RightCubeMaximumNaturality.map

/-- The entire original maximum comparison component is read by the actual inverse chart followed by the
  proved cube maximum. -/
theorem maximumMap_app (n : ℕ) : maximumMap.{u}.app ⦋n⦌ = readCubeMap n ≫ RightCubeMaximum.map n := rfl

end CategoryTheory.CoherentRealization.FixedFrontChart

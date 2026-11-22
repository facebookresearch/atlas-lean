/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontIntervalOperators
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCosimplicial
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightHomCosimplicial

/-!
# Actual cosimplicial naturality of the original right-Hom chart

The constructed cube map follows every genuine right-join operator.
Its actual zero insertion is removed by the proved original front-prefix
composition law, rather than a false strict equality before quotienting.
The whole maps form a genuine cosimplicial natural transformation.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontCubeOperators
open PathLastMaximum PathMaximumOperators FixedFrontCubeMap
variable {n m : ℕ}

/-- The whole actual cube map is natural under each supplied original right-join simplex operator. -/
theorem map_naturality (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    RightCubeCosimplicialMaps.map.{u} θ ≫ cubeMap m = cubeMap n ≫ RightHomResolution.map θ := by
  ext q a
  induction a using _root_.Quotient.inductionOn with
  | _ p =>
    change (intervalMap m 0).app q (p ⋙ RightCubeOperator.functor θ) =
      (RightHomResolution.map θ).app q ((intervalMap n 0).app q p)
    exact (interval_prepend m (θ.toOrderHom 0) q (p ⋙ imageFunctor θ 0)).trans
      (congr($(FixedFrontIntervalOperators.interval_operator θ 0).app q p)).symm

/-- The genuine entire cosimplicial chart map between the constructed original quotient cube and actual
  realized right Hom. -/
def chartMap : RightCubeCosimplicial.diagram.{u} ⟶ RightHomCosimplicial.diagram.{u} where
  app n := cubeMap n.len
  naturality n m θ := map_naturality (n := n.len) (m := m.len) θ

/-- Its original resolving component is exactly the actual cube map, with all original scalar cells unchanged. -/
theorem chartMap_app (n : ℕ) : chartMap.{u}.app ⦋n⦌ = cubeMap n := rfl

end CategoryTheory.CoherentRealization.FixedFrontCubeOperators

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontGadgetDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedBoundaryVertices
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCubeIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCubeOperators
import MathlibExt.CategoryTheory.Enriched.HomEndpointEquality

/-!
# Both SAME original quotient-cube and pointed raw-Hom coefficient directions

The actual complete quotient-cube chart and literal original endpoint
vertices identify each fixed-front raw Hom. All original cosimplicial
operators commute through the genuine enriched endpoint equality square.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The same full original fixed-front pointed source has its literal original structural source vertex. -/
theorem fixedFront_sourceVertex (n : SimplexCategory) :
    OriginalPointed.sourceVertex (plainFixedFrontDiagram.{u}.obj n) = FixedFrontCollapse.source n.len :=
  OriginalPointed.sourceVertex_boundaryOneMap _ _

/-- The same full original fixed-front pointed source has its literal original structural target vertex. -/
theorem fixedFront_targetVertex (n : SimplexCategory) :
    OriginalPointed.targetVertex (plainFixedFrontDiagram.{u}.obj n) = FixedFrontCollapse.target n.len :=
  OriginalPointed.targetVertex_boundaryOneMap _ _

/-- Both full original right-Hom and pointed raw-Hom coefficient directions retain their same original endpoints. -/
def fixedFrontRightHomPointedIso : RightHomCosimplicial.diagram.{u} ≅
    plainFixedFrontDiagram.{u} ⋙ OriginalPointed.homFunctor :=
  NatIso.ofComponents (fun n => eqToIso (congrArg₂
    (fun x y : FixedFrontCollapse.object.{u} n.len _⦋0⦌ => hom (FixedFrontCollapse.object n.len) x y)
      (fixedFront_sourceVertex n).symm (fixedFront_targetVertex n).symm)) (by
    intro n m θ
    exact (EnrichedFunctor.homMap_endpoint_square (realizationMap (FixedFrontOperators.map θ))
      (fixedFront_sourceVertex n).symm (fixedFront_targetVertex n).symm
      (fixedFront_sourceVertex m).symm (fixedFront_targetVertex m).symm
      (FixedFrontVertices.map_source θ) (FixedFrontVertices.map_target θ)
      (OriginalPointed.sourceVertex_map (plainFixedFrontDiagram.map θ))
      (OriginalPointed.targetVertex_map (plainFixedFrontDiagram.map θ))).symm)

/-- The SAME full original quotient cube and pointed raw-Hom cosimplicial diagrams have both complete natural inverse
directions. -/
def fixedFrontCubePointedIso : RightCubeCosimplicial.diagram.{u} ≅
    plainFixedFrontDiagram.{u} ⋙ OriginalPointed.homFunctor :=
  (show RightCubeCosimplicial.diagram.{u} ≅ RightHomCosimplicial.diagram.{u} from
    NatIso.ofComponents (fun n => FixedFrontCubeIso.cubeIso n.len) (by
    intro n m θ
    exact FixedFrontCubeOperators.map_naturality θ)) ≪≫ fixedFrontRightHomPointedIso

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

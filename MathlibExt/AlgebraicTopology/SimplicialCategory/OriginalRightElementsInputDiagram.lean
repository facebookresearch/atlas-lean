/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontRawHomAugmentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontCubePointedIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingPointedDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingRealization

/-!
# The SAME original right-mapping elements and fixed-front raw input diagram

The complete original category-of-elements dictionary and original
pointed Hom isomorphism retain every right-mapping simplex, source
operator and quotient map. The full original quotient-cube chart is
its exact pointed raw-Hom coefficient map, with both inverse directions.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction OriginalGadgetComparison OriginalPointed

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- Every full original right-mapping simplex is its SAME complete original fixed-front input. -/
def rightElementsInputFunctor :
    (SSet.mappingSpaceRight K a b).Elementsᵒᵖ ⥤ CostructuredArrow plainFixedFrontDiagram (pointedInput a b) where
  obj e := CostructuredArrow.mk (toPointedMap a b e.unop.val)
  map {e d} f := CostructuredArrow.homMk f.unop.hom.unop (by
    exact (toPointedMap_operator a b f.unop.hom.unop d.unop.val).trans
      (congrArg (toPointedMap a b) f.unop.map_val))
  map_id e := by apply CostructuredArrow.hom_ext; rfl
  map_comp f g := by apply CostructuredArrow.hom_ext; rfl

/-- Every same original right-mapping element retains its literal whole original quotient input map. -/
theorem rightElementsInputFunctor_input (e : (SSet.mappingSpaceRight K a b).Elementsᵒᵖ) :
    (((rightElementsInputFunctor a b).obj e).hom).right = quotientMap a b e.unop.val := rfl

/-- The SAME actual full original quotient-cube diagram maps by its original entire natural pointed Hom chart. -/
def rightElementsRawCoefficient :
    OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b) ⟶
      rightElementsInputFunctor a b ⋙ fixedFrontRawInputDiagram (pointedInput a b) where
  app e := fixedFrontCubePointedIso.hom.app e.unop.obj.unop
  naturality e d f := by
    have h : RightCubeCosimplicialMaps.map f.unop.hom.unop ≫ fixedFrontCubePointedIso.hom.app d.unop.obj.unop =
        fixedFrontCubePointedIso.hom.app e.unop.obj.unop ≫
          homFunctor.map (plainFixedFrontDiagram.map f.unop.hom.unop) :=
      fixedFrontCubePointedIso.hom.naturality f.unop.hom.unop
    exact h

/-- Both complete original coefficient directions are the SAME original full quotient-cube chart at every original
mapping element. -/
def rightElementsRawCoefficientIso :
    OriginalRightCubeRealization.diagram (SSet.mappingSpaceRight K a b) ≅
      rightElementsInputFunctor a b ⋙ fixedFrontRawInputDiagram (pointedInput a b) :=
  NatIso.ofComponents (fun e => fixedFrontCubePointedIso.app e.unop.obj.unop)
    (by
      intro e d f
      have h : RightCubeCosimplicialMaps.map f.unop.hom.unop ≫ fixedFrontCubePointedIso.hom.app d.unop.obj.unop =
          fixedFrontCubePointedIso.hom.app e.unop.obj.unop ≫
            homFunctor.map (plainFixedFrontDiagram.map f.unop.hom.unop) :=
        fixedFrontCubePointedIso.hom.naturality f.unop.hom.unop
      exact h)

end CategoryTheory.CoherentRealization.OriginalRawRightMapping

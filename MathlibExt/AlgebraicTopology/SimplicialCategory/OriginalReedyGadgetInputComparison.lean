/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontGadgetDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedQuasiReplacementRetraction
import MathlibExt.AlgebraicTopology.SimplicialObject.CosimplicialHomInputWeak

/-!
# The SAME original Reedy and fixed-front full gadget input comparison

The original generated pointed Reedy map gives a full natural
transformation on the actual input categories over the same original
target. Every input triangle and every original ordinal arrow is kept.
Its full original input restriction is weak at quasicategory targets.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The same full original Reedy input functor to the entire actual gadget category. -/
def reedyIntoGadgetInputs (X : OriginalPointed.Category.{u}) :
    CostructuredArrow plainReedyDiagram X ⥤ CostructuredArrow OriginalPointed.gadgetInclusion X :=
  reedyIntoFibrantGadgetInputs X ⋙ OriginalPointed.fibrantInputInclusion X

/-- The SAME original full Reedy input restriction retains every original source object, arrow and map. -/
def reedyInputRestriction (X : OriginalPointed.Category.{u}) :
    CostructuredArrow plainReedyDiagram X ⥤ CostructuredArrow plainFixedFrontDiagram X :=
  CosimplicialObject.inputRestriction plainReedyMap X

/-- The same entire original generated Reedy map gives the complete original input natural transformation over the same
target. -/
def reedyInputGadgetComparison (X : OriginalPointed.Category.{u}) :
    reedyInputRestriction X ⋙ fixedFrontIntoGadgetInputs X ⟶ reedyIntoGadgetInputs X where
  app s := CostructuredArrow.homMk (ObjectProperty.homMk (plainReedyMap.app s.left)) (by
    change plainReedyMap.app s.left ≫ s.hom = ((reedyInputRestriction X).obj s).hom
    exact (CosimplicialObject.inputRestriction_hom plainReedyMap X s).symm)
  naturality s t f := by
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    exact plainReedyMap.naturality f.left

/-- The SAME original full Reedy input nerve restriction is weak at every actual original quasicategory target. -/
theorem reedyInputRestriction_nerve_weak (X : OriginalPointed.Category.{u}) [SSet.Quasicategory X.right] :
    SSet.realizationWeakEquivalences (nerveMap (reedyInputRestriction X)) :=
  CosimplicialObject.inputRestriction_nerve_weak plainReedyMap X (plainReedyHomRestriction_weak X)

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

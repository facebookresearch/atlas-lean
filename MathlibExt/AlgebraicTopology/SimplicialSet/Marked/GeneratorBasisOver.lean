/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.GeneratorBasisDensity
import Mathlib.CategoryTheory.Limits.Over

/-!
# The original marked basis presentation over the same base

The proven marked total-space presentation lifts along its exact
original base map. Native slice colimit creation retains the same
total objects, markings, complete basis maps and base equations. No
Kan or quasicategory assumption is needed for this presentation.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked.GeneratorBasis

/-- The whole original marked basis diagram lies over the same supplied base through its original maps. -/
def overDiagram {Z : Marked.{u}} (X : Over Z) : Index X.left ⥤ Over Z :=
  Over.lift (diagram X.left) ((cocone X.left).ι ≫ (Functor.const (Index X.left)).map X.hom)

/-- The original marked cocone lifts with precisely the same total space and original projection. -/
def overCocone {Z : Marked.{u}} (X : Over Z) : Cocone (overDiagram X) :=
  Over.liftCocone (cocone X.left) X.hom

/-- The native same-base marked basis cocone is a genuine colimit, by actual slice colimit creation. -/
def overIsColimit {Z : Marked.{u}} (X : Over Z) : IsColimit (overCocone X) :=
  Over.isColimitLiftCocone (cocone X.left) X.hom (isColimit X.left)

/-- The lifted presentation retains the original entire marked total object. -/
theorem overCocone_total {Z : Marked.{u}} (X : Over Z) : (overCocone X).pt.left = X.left := rfl

/-- The lifted presentation retains precisely the original entire base projection. -/
theorem overCocone_projection {Z : Marked.{u}} (X : Over Z) : (overCocone X).pt.hom = X.hom := rfl

/-- Each lifted basis leg is the same entire original marked total-space map. -/
theorem overCocone_ι_left {Z : Marked.{u}} (X : Over Z) (i : Index X.left) :
    ((overCocone X).ι.app i).left = i.hom := rfl

end SSet.Marked.GeneratorBasis

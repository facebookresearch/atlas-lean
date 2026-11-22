/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingNaturality
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# The SAME original quotient-cube realization over every original simplex

The full category of elements retains every original cell of the
supplied simplicial set. Its opposite diagram evaluates the SAME
original cosimplicial quotient cubes and every original operator.
The genuine colimit retains all coefficients and source-map laws.
-/

noncomputable section
universe u
open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- The entire original quotient-cube diagram indexed by all original simplices. -/
def diagram (K : SSet.{u}) : K.Elementsᵒᵖ ⥤ SSet.{u} :=
  (Functor.Elements.π K).leftOp ⋙ RightCubeCosimplicial.diagram.{u}

/-- Each original element has precisely the SAME original coefficient cube. -/
theorem diagram_obj (K : SSet.{u}) (e : K.Elementsᵒᵖ) :
    (diagram K).obj e = RightCubeRelations.object.{u} e.unop.obj.unop.len := rfl

/-- Every entire original element arrow acts by its SAME original cosimplicial cube operator. -/
theorem diagram_map (K : SSet.{u}) {e d : K.Elementsᵒᵖ} (f : e ⟶ d) :
    (diagram K).map f = RightCubeCosimplicialMaps.map f.unop.hom.unop := rfl

/-- The genuine original full quotient-cube realization, retaining all original coefficients. -/
def object (K : SSet.{u}) : SSet.{u} := colimit (diagram K)

/-- The SAME full original coefficient insertion into that genuine colimit. -/
def insertion (K : SSet.{u}) (e : K.Elementsᵒᵖ) :
    (diagram K).obj e ⟶ object K := colimit.ι (diagram K) e

/-- The whole original coefficient insertion retains every same original ordinal arrow. -/
theorem insertion_naturality (K : SSet.{u}) {e d : K.Elementsᵒᵖ} (f : e ⟶ d) :
    (diagram K).map f ≫ insertion K d = insertion K e := colimit.w (diagram K) f

/-- The actual original element-map cocone of a supplied original simplicial map. -/
def mapCocone {K L : SSet.{u}} (f : K ⟶ L) : Cocone (diagram K) where
  pt := object L
  ι := {
    app e := insertion L (f.mapElements.op.obj e)
    naturality e d g := by
      change (diagram K).map g ≫ insertion L (f.mapElements.op.obj d) =
        insertion L (f.mapElements.op.obj e) ≫ 𝟙 _
      exact (insertion_naturality L (f.mapElements.op.map g)).trans (Category.comp_id _).symm }

/-- The SAME original simplex map gives its full original realized quotient-cube map. -/
def map {K L : SSet.{u}} (f : K ⟶ L) : object K ⟶ object L :=
  colimit.desc (diagram K) (mapCocone f)

/-- Every actual original coefficient is retained by the SAME full original realized source map. -/
theorem insertion_map {K L : SSet.{u}} (f : K ⟶ L) (e : K.Elementsᵒᵖ) :
    insertion K e ≫ map f = insertion L (f.mapElements.op.obj e) :=
  colimit.ι_desc (mapCocone f) e

/-- The original full quotient-cube realization preserves the actual identity simplicial map. -/
theorem map_id (K : SSet.{u}) : map (𝟙 K) = 𝟙 (object K) := by
  apply colimit.hom_ext
  intro e
  exact (insertion_map (𝟙 K) e).trans (Category.comp_id _).symm

/-- The original full quotient-cube realization preserves the actual complete composite simplicial map. -/
theorem map_comp {K L M : SSet.{u}} (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := by
  apply colimit.hom_ext
  intro e
  exact (insertion_map (f ≫ g) e).trans
    ((insertion_map g (f.mapElements.op.obj e)).symm.trans
      ((congrArg (fun q => q ≫ map g) (insertion_map f e).symm).trans (Category.assoc _ _ _)))

/-- The genuine entire original quotient-cube realization functor, with every original cell map. -/
def functor : SSet.{u} ⥤ SSet.{u} where
  obj := object
  map := map
  map_id := map_id
  map_comp := map_comp

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomFunctor
import Mathlib.CategoryTheory.Filtered.Final

/-!
# The same filtered Hom diagram on the under-source tail

Each indexing arrow out of j gives its complete 
enriched functor. The full Under triangle and functor laws
retain every source object, Hom map and ordinal coefficient.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u}) (j : J)

/-- The complete diagram under its same source enrichment. -/
def sourceDiagram : Under j ⥤ Under (F.obj j) where
  obj a := Under.mk (F.map a.hom)
  map f := Under.homMk (F.map f.right)
    ((F.map_comp _ _).symm.trans (congrArg F.map (Under.w f)))
  map_id a := by
    apply Under.UnderMorphism.ext
    exact F.map_id a.right
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact F.map_comp f.right g.right

/-- The same full stage Hom diagram at the images of the two source
Objects. -/
def homDiagram (x y : F.obj j) : Under j ⥤ SSet.{u} :=
  sourceDiagram F j ⋙ OriginalUnderHom.functor (F.obj j) x y

/-- Every Hom object is read back at the same diagram-arrow images. -/
theorem homDiagram_obj (x y : F.obj j) (a : Under j) :
    (homDiagram F j x y).obj a = ((F.map a.hom).obj x ⟶[SSet.{u}] (F.map a.hom).obj y) := rfl

end CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom

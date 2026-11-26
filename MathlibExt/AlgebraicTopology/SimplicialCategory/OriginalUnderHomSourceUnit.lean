/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomEqualityTransport

/-!
# The complete Hom source unit on an under-category diagram

Every coefficient is the root Hom map. The same full
under-root triangle proves its naturality and the exact terminal cocone
square. The diagram object and Hom universes are independent, and no
fibrancy, weakness or colimit outcome is assumed.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalUnderHom

variable {C : Carrier.{u}} {J : Type v} [Category.{w} J]
  (U : J ⥤ Under C) (x y : C)

/-- The full under-root Hom map satisfies its same complete triangle. -/
theorem rootMap_triangle {A B : Under C} (f : A ⟶ B) :
    A.hom.map x y ≫ map C x y f = B.hom.map x y := by
  have h := EnrichedFunctor.homMap_transport_of_eq (Under.w f) x y
  let t := congrArg₂ (fun a b : B.right => a ⟶[SSet.{u}] b) (endpoint C f x) (endpoint C f y)
  change (A.hom.map x y ≫ f.right.map (A.hom.obj x) (A.hom.obj y)) ≫ eqToHom t =
    B.hom.map x y at h
  change A.hom.map x y ≫ (f.right.map (A.hom.obj x) (A.hom.obj y) ≫ eqToHom t) =
    B.hom.map x y
  exact (Category.assoc _ _ _).symm.trans h

/-- The root maps give the complete source-unit natural transformation. -/
def sourceUnit : (Functor.const J).obj (x ⟶[SSet.{u}] y) ⟶ U ⋙ functor C x y where
  app i := (U.obj i).hom.map x y
  naturality _i _j f := (Category.id_comp _).trans (rootMap_triangle x y (U.map f)).symm

/-- Read each coefficient as precisely the same complete root Hom map. -/
theorem sourceUnit_app (i : J) : (sourceUnit U x y).app i = (U.obj i).hom.map x y := rfl

/-- Every cocone retains the complete same source-unit square. -/
theorem sourceUnit_cocone (s : Cocone U) (i : J) :
    (sourceUnit U x y).app i ≫ ((functor C x y).mapCocone s).ι.app i =
      s.pt.hom.map x y :=
  rootMap_triangle x y (s.ι.app i)

end CategoryTheory.SimplicialEnrichment.OriginalUnderHom

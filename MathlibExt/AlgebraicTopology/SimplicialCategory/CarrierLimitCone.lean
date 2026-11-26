/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLimitLabelDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLimits

/-!
# The changing-object enriched limit cone

Take the native limit of the same object diagram, reindex the
full enrichments at its compatible individual objects, and
take the Hom limit. The full cone projections
retain those object functions and complete scalar limit maps.
Their enriched naturality holds for every indexing arrow.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierLimit
open FixedObjects

variable {J : Type v} [SmallCategory J] (F : J ⥤ Carrier.{u})
variable [HasLimit (F ⋙ forgetObjects)] [HasLimitsOfShape J SSet.{u}]

/-- The native limit of the individual-object diagram. -/
abbrev labels : Type u := limit (F ⋙ forgetObjects)

/-- The full enrichment diagram at those same compatible object labels. -/
abbrev diagram : J ⥤ FixedObjects (labels F) :=
  CarrierLimitLabelDiagram.functor F (limit.cone (F ⋙ forgetObjects))

/-- The simplicial enrichment on the limit of the diagram’s object types. -/
abbrev fixedObject : FixedObjects (labels F) := HomLimit.object (diagram F)

/-- The candidate changing-object enriched limit. -/
abbrev object : Carrier.{u} := (fixedObject F).val

/-- Its individual objects correspond exactly to the native object
limit. -/
def objectsEquiv : object F ≃ labels F := (verticesEquiv (fixedObject F)).symm

/-- The limit Hom is the native scalar limit at those same labels. -/
theorem object_hom (x y : labels F) :
    hom (fixedObject F) x y = limit (homDiagram (diagram F) x y) := rfl

/-- The enriched projection through the same scalar Hom-limit leg. -/
def projection (j : J) : object F ⟶ F.obj j :=
  (HomLimit.projection (diagram F) j).val ≫
    CarrierLimitLabelDiagram.projection F (limit.cone (F ⋙ forgetObjects)) j

/-- Each full projection has the literal native object-limit component. -/
theorem projection_obj (j : J) (x : labels F) :
    (projection F j).obj (vertex (fixedObject F) x) = (limit.π (F ⋙ forgetObjects) j) x :=
  congrArg (CarrierLimitLabelDiagram.label F (limit.cone (F ⋙ forgetObjects)) j)
    (map_vertex (HomLimit.projection (diagram F) j) x)

private theorem heq_comp_eqToHom {A B C : SSet.{u}} (f : A ⟶ B) (h : B = C) :
    HEq (f ≫ eqToHom h) f := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

/-- The projection Hom is literally the same complete scalar limit leg, with
its dependent
endpoints retained. -/
theorem projection_hom (j : J) (x y : labels F) :
    HEq ((projection F j).map (vertex (fixedObject F) x) (vertex (fixedObject F) y))
      (limit.π (homDiagram (diagram F) x y) j) := by
  let p := HomLimit.projection (diagram F) j
  let e : (p.val.obj (vertex (fixedObject F) x) ⟶[SSet.{u}]
      p.val.obj (vertex (fixedObject F) y)) = hom ((diagram F).obj j) x y := by
    rw [map_vertex p x, map_vertex p y]
  have h : HEq (p.val.map (vertex (fixedObject F) x) (vertex (fixedObject F) y))
      (limit.π (homDiagram (diagram F) x y) j) :=
    (heq_comp_eqToHom _ e).symm.trans
      (heq_of_eq (HomLimit.homMap_projection (diagram F) j x y))
  change HEq (p.val.map (vertex (fixedObject F) x) (vertex (fixedObject F) y) ≫ 𝟙 _)
    (limit.π (homDiagram (diagram F) x y) j)
  exact (heq_of_eq (Category.comp_id _)).trans h

/-- The same varying-object enrichment has a full cone over every
diagram arrow. -/
def cone : Cone F where
  pt := object F
  π := {
    app := projection F
    naturality j k f := by
      change 𝟙 (object F) ≫ projection F k = projection F j ≫ F.map f
      have h : (HomLimit.projection (diagram F) j).val ≫ ((diagram F).map f).val =
          (HomLimit.projection (diagram F) k).val :=
        congrArg (fun G : fixedObject F ⟶ (diagram F).obj k =>
          G.val) ((HomLimit.cone (diagram F)).w f)
      exact (Category.id_comp _).trans
        ((congrArg (fun G => G ≫ CarrierLimitLabelDiagram.projection F
          (limit.cone (F ⋙ forgetObjects)) k) h.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun G => (HomLimit.projection (diagram F) j).val ≫ G)
              (CarrierLimitLabelDiagram.projection_naturality F (limit.cone (F ⋙
                forgetObjects)) f)).trans
                (Category.assoc _ _ _).symm))) }

end CategoryTheory.SimplicialEnrichment.CarrierLimit

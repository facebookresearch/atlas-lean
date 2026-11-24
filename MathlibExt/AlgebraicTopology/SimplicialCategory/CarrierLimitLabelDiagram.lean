/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelReadback

/-!
# The actual fixed-cone-label diagram of changing-object enrichments

The entire original object cone supplies its compatible individual
labels. Reindex each whole enrichment at those exact labels, with the
identity Hom projections. Original cone equations give every complete
diagram map, its functor laws, and all original scalar Hom readbacks.
This is the input to genuine varying-object enriched limits.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierLimitLabelDiagram
open FixedObjects

variable {J : Type v} [SmallCategory J] (F : J ⥤ Carrier.{u})
variable (s : Cone (F ⋙ forgetObjects))

/-- Each actual compatible object-cone label keeps its individual original image. -/
def label (j : J) : s.pt → F.obj j := s.π.app j

/-- The entire original enrichment reindexed at the exact compatible cone labels. -/
abbrev object (j : J) : FixedObjects s.pt :=
  CarrierReindexing.object (F.obj j) (label F s j)

/-- Its whole original projection keeps the actual object function and identity Hom maps. -/
def projection (j : J) : (object F s j).val ⟶ F.obj j :=
  CarrierReindexing.toTarget (F.obj j) (label F s j)

/-- The supplied original object cone gives the exact object equation of every original
diagram map. -/
theorem input_object_eq {j k : J} (f : j ⟶ k) (x : s.pt) :
    (projection F s j ≫ F.map f).obj (vertex (object F s j) x) = label F s k x := by
  exact ConcreteCategory.congr_hom (C := Type u) (s.w f) x

/-- Reindex the complete original diagram map at its SAME compatible cone-label equations. -/
def map {j k : J} (f : j ⟶ k) : object F s j ⟶ object F s k :=
  CarrierLabelReadback.map (object F s j) (label F s k)
    (projection F s j ≫ F.map f) (input_object_eq F s f)

/-- Projection recovers the SAME whole original diagram functor at every arrow. -/
theorem projection_naturality {j k : J} (f : j ⟶ k) :
    (map F s f).val ≫ projection F s k = projection F s j ≫ F.map f :=
  CarrierLabelReadback.map_fac (object F s j) (label F s k)
    (projection F s j ≫ F.map f) (input_object_eq F s f)

/-- Every scalar operator of the original Hom map is retained with only the actual cone
endpoint equations. -/
theorem homMap_map {j k : J} (f : j ⟶ k) (x y : s.pt) :
    homMap (map F s f) x y =
      (F.map f).map (label F s j x) (label F s j y) ≫
        eqToHom (congrArg₂ (fun a b : F.obj k => a ⟶[SSet.{u}] b)
          (input_object_eq F s f x) (input_object_eq F s f y)) := by
  exact (CarrierLabelReadback.homMap_map (object F s j) (label F s k)
    (projection F s j ≫ F.map f) (input_object_eq F s f) x y).trans (by
      change (𝟙 _ ≫ (F.map f).map (label F s j x) (label F s j y)) ≫ eqToHom _ = _
      exact congrArg (fun G => G ≫ eqToHom
        (congrArg₂ (fun a b : F.obj k => a ⟶[SSet.{u}] b)
          (input_object_eq F s f x) (input_object_eq F s f y)))
        (Category.id_comp ((F.map f).map (label F s j x) (label F s j y))))

/-- The complete original changing-object diagram on its actual compatible cone labels. -/
def functor : J ⥤ FixedObjects s.pt where
  obj := object F s
  map := map F s
  map_id j := by
    apply CarrierLabelMaps.projection_injective (label F s j)
    change (map F s (𝟙 j)).val ≫ projection F s j = 𝟙 (object F s j).val ≫ projection F s j
    exact (projection_naturality F s (𝟙 j)).trans
      ((congrArg (fun G => projection F s j ≫ G) (F.map_id j)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  map_comp {j k l} f g := by
    apply CarrierLabelMaps.projection_injective (label F s l)
    change (map F s (f ≫ g)).val ≫ projection F s l =
      ((map F s f).val ≫ (map F s g).val) ≫ projection F s l
    have hleft := (projection_naturality F s (f ≫ g)).trans
      (congrArg (fun G => projection F s j ≫ G) (F.map_comp f g))
    have hright : ((map F s f).val ≫ (map F s g).val) ≫ projection F s l =
        projection F s j ≫ (F.map f ≫ F.map g) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun G => (map F s f).val ≫ G) (projection_naturality F s g)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun G => G ≫ F.map g) (projection_naturality F s f)).trans
              (Category.assoc _ _ _))))
    exact hleft.trans hright.symm

end CategoryTheory.SimplicialEnrichment.CarrierLimitLabelDiagram

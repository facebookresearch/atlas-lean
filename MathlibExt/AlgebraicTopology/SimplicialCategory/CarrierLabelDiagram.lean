/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelUniversalProperty

/-! # The actual fixed-target-label diagram of changing-object enrichments

An original object cocone supplies its actual label maps. Each original
enrichment is pushed forward to those same target labels. The original
diagram functors extend by their proved object equations; their full
identity and composition laws give the resulting fixed-object diagram.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierLabelDiagram
open FixedObjects

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u})
variable (s : Cocone (F ⋙ forgetObjects))

/-- Each actual original object has its specified cocone label. -/
def label (j : J) : F.obj j → s.pt := s.ι.app j

/-- Push forward the entire original enrichment to the actual cocone labels. -/
abbrev object (j : J) : FixedObjects s.pt :=
  CarrierLabelExtension.object (F.obj j) (label F s j)

/-- The same original whole source-generator leg at its cocone label map. -/
def leg (j : J) : F.obj j ⟶ (object F s j).val :=
  CarrierLabelExtension.inclusion (F.obj j) (label F s j)

/-- The actual whole original diagram map has its same prescribed target-label equation. -/
theorem input_object_eq {j k : J} (f : j ⟶ k) :
    (F.map f ≫ leg F s k).obj = fun x => vertex (object F s k) (label F s j x) := by
  funext x
  have hx := ConcreteCategory.congr_hom (C := Type u) (s.w f) x
  change label F s k ((F.map f).obj x) = label F s j x at hx
  exact (CarrierLabelExtension.inclusion_obj (F.obj k) (label F s k) ((F.map f).obj x)).trans
    (congrArg (vertex (object F s k)) hx)

/-- The original changing-object diagram map with its actual source-label boundary. -/
def input {j k : J} (f : j ⟶ k) : CarrierReindexing.source (F.obj j) ⟶
    LabelRestriction.object (label F s j) (object F s k) :=
  CarrierLabelMaps.ofObjectEquation (fun x => vertex (object F s k) (label F s j x))
    (F.map f ≫ leg F s k) (input_object_eq F s f)

/-- Extend the original whole diagram functor to the fixed-target-label path sources. -/
def map {j k : J} (f : j ⟶ k) : object F s j ⟶ object F s k :=
  LabelPushforward.desc (label F s j) (CarrierReindexing.source (F.obj j)) (input F s f)

/-- The same entire original source functor is retained by every pushed-forward diagram map. -/
theorem leg_naturality {j k : J} (f : j ⟶ k) :
    leg F s j ≫ (map F s f).val = F.map f ≫ leg F s k :=
  (CarrierLabelUniversalProperty.desc_fac (F.obj j) (label F s j) (input F s f)).trans
    (CarrierLabelMaps.ofObjectEquation_fac
      (fun x => vertex (object F s k) (label F s j x))
      (F.map f ≫ leg F s k) (input_object_eq F s f))

/-- The actual entire diagram on the same target labels, with both full functor laws proved. -/
def functor : J ⥤ FixedObjects s.pt where
  obj := object F s
  map := map F s
  map_id j := by
    apply CarrierLabelUniversalProperty.precomposition_injective (F.obj j) (label F s j)
    change leg F s j ≫ (map F s (𝟙 j)).val = leg F s j ≫ 𝟙 (object F s j).val
    exact (leg_naturality F s (𝟙 j)).trans
      ((congrArg (fun k => k ≫ leg F s j) (F.map_id j)).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm))
  map_comp {j k l} f g := by
    apply CarrierLabelUniversalProperty.precomposition_injective (F.obj j) (label F s j)
    change leg F s j ≫ (map F s (f ≫ g)).val =
      leg F s j ≫ ((map F s f).val ≫ (map F s g).val)
    have hl := (leg_naturality F s (f ≫ g)).trans
      (congrArg (fun h => h ≫ leg F s l) (F.map_comp f g))
    have hr : leg F s j ≫ ((map F s f).val ≫ (map F s g).val) =
        (F.map f ≫ F.map g) ≫ leg F s l :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ (map F s g).val) (leg_naturality F s f)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun h => F.map f ≫ h) (leg_naturality F s g)).trans
              (Category.assoc _ _ _).symm)))
    exact hl.trans hr.symm

end CategoryTheory.SimplicialEnrichment.CarrierLabelDiagram

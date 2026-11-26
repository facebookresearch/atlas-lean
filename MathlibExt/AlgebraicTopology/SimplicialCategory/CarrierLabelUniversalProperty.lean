/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelExtension

/-!
# The universal property of label pushforward

A map from the label pushforward is uniquely determined by its restriction
to the source enrichment. Extension and restriction preserve the object
labels and all Hom maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierLabelUniversalProperty
open FixedObjects CarrierLabelExtension

variable (C : Carrier.{u}) {O : Type u} (a : C → O)
variable {D : FixedObjects O}

/-- Projecting the restricted unit composition retains the same carrier map. -/
theorem unit_projection (G : object C a ⟶ D) :
    (LabelPushforward.unit a (CarrierReindexing.source C) ≫ LabelRestriction.map a G).val ≫
        CarrierReindexing.toTarget D.val (fun s => vertex D (a s)) =
      inclusion C a ≫ G.val := by
  change ((LabelPushforward.unit a (CarrierReindexing.source C)).val ≫
      (LabelRestriction.map a G).val) ≫
      CarrierReindexing.toTarget D.val (fun s => vertex D (a s)) =
    ((LabelPushforward.unit a (CarrierReindexing.source C)).val ≫
      CarrierReindexing.toTarget (object C a).val (fun s => vertex (object C a) (a s))) ≫ G.val
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (LabelPushforward.unit a (CarrierReindexing.source C)).val ≫ k)
      (restriction_projection a G)).trans (Category.assoc _ _ _).symm)

/-- The carrier extension factors the same supplied source map. -/
theorem desc_fac (F : CarrierReindexing.source C ⟶ LabelRestriction.object a D) :
    inclusion C a ≫ (LabelPushforward.desc a (CarrierReindexing.source C) F).val =
      F.val ≫ CarrierReindexing.toTarget D.val (fun s => vertex D (a s)) := by
  have h := congrArg
    (fun H : CarrierReindexing.source C ⟶ LabelRestriction.object a D =>
      H.val ≫ CarrierReindexing.toTarget D.val (fun s => vertex D (a s)))
    (LabelPushforward.unit_desc a (CarrierReindexing.source C) F)
  exact (unit_projection C a (LabelPushforward.desc a (CarrierReindexing.source C) F)).symm.trans h

/-- Fixed-target-label maps are determined by their generator unit. -/
theorem precomposition_injective :
    Function.Injective (fun G : object C a ⟶ D => inclusion C a ≫ G.val) := by
  intro F G h
  apply (LabelPushforward.homEquiv a (CarrierReindexing.source C) D).injective
  change LabelPushforward.unit a (CarrierReindexing.source C) ≫ LabelRestriction.map a F =
    LabelPushforward.unit a (CarrierReindexing.source C) ≫ LabelRestriction.map a G
  apply CarrierLabelMaps.projection_injective (fun s => vertex D (a s))
  exact (unit_projection C a F).trans (h.trans (unit_projection C a G).symm)

/-- Every extension retaining the supplied source map is the canonical extension. -/
theorem desc_unique (F : CarrierReindexing.source C ⟶ LabelRestriction.object a D)
    (G : object C a ⟶ D)
    (h : inclusion C a ≫ G.val =
      F.val ≫ CarrierReindexing.toTarget D.val (fun s => vertex D (a s))) :
    G = LabelPushforward.desc a (CarrierReindexing.source C) F :=
  precomposition_injective C a (h.trans (desc_fac C a F).symm)

end CategoryTheory.SimplicialEnrichment.CarrierLabelUniversalProperty

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelExtension

/-! # Whole carrier maps satisfy the actual label-source universal property

The fixed-object universal map is interpreted in the original carrier.
The exact reindexing projections retain every original input map.
Uniqueness is proved from those whole functors and all original generators.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierLabelUniversalProperty
open FixedObjects CarrierLabelExtension

variable (C : Carrier.{u}) {O : Type u} (a : C → O)
variable {D : FixedObjects O}

/-- Projecting the whole restricted unit composition retains the same original carrier map. -/
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

/-- The actual original carrier extension factors the same whole supplied source map. -/
theorem desc_fac (F : CarrierReindexing.source C ⟶ LabelRestriction.object a D) :
    inclusion C a ≫ (LabelPushforward.desc a (CarrierReindexing.source C) F).val =
      F.val ≫ CarrierReindexing.toTarget D.val (fun s => vertex D (a s)) := by
  have h := congrArg
    (fun H : CarrierReindexing.source C ⟶ LabelRestriction.object a D =>
      H.val ≫ CarrierReindexing.toTarget D.val (fun s => vertex D (a s)))
    (LabelPushforward.unit_desc a (CarrierReindexing.source C) F)
  exact (unit_projection C a (LabelPushforward.desc a (CarrierReindexing.source C) F)).symm.trans h

/-- Whole fixed-target-label maps are determined by their actual original generator unit. -/
theorem precomposition_injective :
    Function.Injective (fun G : object C a ⟶ D => inclusion C a ≫ G.val) := by
  intro F G h
  apply (LabelPushforward.homEquiv a (CarrierReindexing.source C) D).injective
  change LabelPushforward.unit a (CarrierReindexing.source C) ≫ LabelRestriction.map a F =
    LabelPushforward.unit a (CarrierReindexing.source C) ≫ LabelRestriction.map a G
  apply CarrierLabelMaps.projection_injective (fun s => vertex D (a s))
  exact (unit_projection C a F).trans (h.trans (unit_projection C a G).symm)

/-- Every whole extension retaining the supplied original source map is the canonical extension. -/
theorem desc_unique (F : CarrierReindexing.source C ⟶ LabelRestriction.object a D)
    (G : object C a ⟶ D)
    (h : inclusion C a ≫ G.val =
      F.val ≫ CarrierReindexing.toTarget D.val (fun s => vertex D (a s))) :
    G = LabelPushforward.desc a (CarrierReindexing.source C) F :=
  precomposition_injective C a (h.trans (desc_fac C a F).symm)

end CategoryTheory.SimplicialEnrichment.CarrierLabelUniversalProperty

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelExtension
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelReadback

/-!
# The label-pushforward unit on every fixed-label source

The source may have any fixed-fiber presentation. Its
carrier unit, source maps and generator universal property
are retained, including all endpoint-label equalities.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward

variable {A O : Type u} (a : A → O) (C : FixedObjects A)

/-- The same carrier unit of the label-pushforward source. -/
def carrierUnit : C.val ⟶ (object a C).val :=
  (unit a C).val ≫ CarrierReindexing.toTarget (object a C).val
    (fun s => vertex (object a C) (a s))

/-- Every source vertex has precisely its prescribed target label. -/
theorem carrierUnit_vertex (s : A) :
    (carrierUnit a C).obj (vertex C s) = vertex (object a C) (a s) :=
  congrArg (fun t => vertex (object a C) (a t)) (map_vertex (unit a C) s)

variable {D : FixedObjects O}

/-- The complete restricted unit square retains the same full carrier map. -/
theorem carrierUnit_projection (G : object a C ⟶ D) :
    (unit a C ≫ LabelRestriction.map a G).val ≫
      CarrierReindexing.toTarget D.val (fun s => vertex D (a s)) =
        carrierUnit a C ≫ G.val := by
  change ((unit a C).val ≫ (LabelRestriction.map a G).val) ≫
    CarrierReindexing.toTarget D.val (fun s => vertex D (a s)) =
      ((unit a C).val ≫ CarrierReindexing.toTarget (object a C).val
        (fun s => vertex (object a C) (a s))) ≫ G.val
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (unit a C).val ≫ k)
      (CarrierLabelExtension.restriction_projection a G)).trans (Category.assoc _ _ _).symm)

/-- The same source functor is recovered from the presented descender. -/
theorem carrierUnit_desc (F : C ⟶ LabelRestriction.object a D) :
    carrierUnit a C ≫ (desc a C F).val =
      F.val ≫ CarrierReindexing.toTarget D.val (fun s => vertex D (a s)) := by
  have h := congrArg (fun G : C ⟶ LabelRestriction.object a D =>
    G.val ≫ CarrierReindexing.toTarget D.val (fun s => vertex D (a s))) (unit_desc a C F)
  exact (carrierUnit_projection a C (desc a C F)).symm.trans h

/-- The fixed-label target map is determined by its same carrier unit. -/
theorem carrierUnit_ext :
    Function.Injective (fun G : object a C ⟶ D => carrierUnit a C ≫ G.val) := by
  intro F G h
  apply (homEquiv a C D).injective
  apply CarrierLabelMaps.projection_injective (fun s => vertex D (a s))
  exact (carrierUnit_projection a C F).trans (h.trans (carrierUnit_projection a C G).symm)

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward

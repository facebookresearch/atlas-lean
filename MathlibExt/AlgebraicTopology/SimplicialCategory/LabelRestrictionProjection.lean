/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelReadback

/-!
# Natural projections of fixed-label restriction

The restriction has its identityHom projection to the
enrichment. Every complete restricted functor is the same
canonical readback through its label equations. Thus both
naturality legs retain their object functions and Homs.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelRestriction

variable {A O : Type u} (a : A → O)

/-- The same projection at the supplied individual label images. -/
def projection (D : FixedObjects O) : (object a D).val ⟶ D.val :=
  CarrierReindexing.toTarget D.val (fun s => vertex D (a s))

/-- Its object function is the literal supplied label map. -/
theorem projection_obj (D : FixedObjects O) (s : A) :
    (projection a D).obj s = vertex D (a s) := rfl

/-- The restricted functor has exactly its same target label equation. -/
theorem map_object_eq {C D : FixedObjects O} (F : C ⟶ D) (s : A) :
    (projection a C ≫ F.val).obj (vertex (object a C) s) = vertex D (a s) :=
  map_vertex F (a s)

/-- The restricted functor is precisely the canonical full readback of that
same projected functor. -/
theorem map_as_readback {C D : FixedObjects O} (F : C ⟶ D) :
    map a F = CarrierLabelReadback.map (object a C) (fun s => vertex D (a s))
      (projection a C ≫ F.val) (map_object_eq a F) := by
  apply homMaps_ext
  intro s t
  have h := CarrierLabelReadback.homMap_map (object a C) (fun x => vertex D (a x))
    (projection a C ≫ F.val) (map_object_eq a F) s t
  have h' : CarrierLabelReadback.originalHom (object a C) (fun x => vertex D (a x))
      (projection a C ≫ F.val) (map_object_eq a F) s t = homMap F (a s) (a t) := by
    change (𝟙 _ ≫ F.val.map (vertex C (a s)) (vertex C (a t))) ≫ eqToHom _ =
      F.val.map (vertex C (a s)) (vertex C (a t)) ≫ eqToHom _
    exact congrArg (fun G => G ≫ eqToHom
      (by rw [map_vertex F (a s), map_vertex F (a t)]; rfl))
      (Category.id_comp (F.val.map (vertex C (a s)) (vertex C (a t))))
  exact (homMap_map a F s t).trans (h.trans h').symm

/-- Full restriction and projection retain the exact enriched naturality square. -/
theorem projection_naturality {C D : FixedObjects O} (F : C ⟶ D) :
    (map a F).val ≫ projection a D = projection a C ≫ F.val :=
  (congrArg (fun G : object a C ⟶ object a D => G.val ≫ projection a D)
    (map_as_readback a F)).trans
      (CarrierLabelReadback.map_fac (object a C) (fun s => vertex D (a s))
        (projection a C ≫ F.val) (map_object_eq a F))

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelRestriction

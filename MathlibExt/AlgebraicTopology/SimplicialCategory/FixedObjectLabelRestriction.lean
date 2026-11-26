/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierReindexing
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps

/-! # Enriched restriction along an arbitrary label map

The reindexed target is used literally. Its Hom objects, units
and compositions are the target values at the supplied images.
Fixed-object functors restrict to those same Hom maps. No injectivity,
surjectivity, fibrancy or model-comparison outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelRestriction

variable {A O : Type u} (a : A → O)

/-- Reindex the enrichment along the specified object function. -/
def object (D : FixedObjects O) : FixedObjects A :=
  CarrierReindexing.object D.val (fun s => vertex D (a s))

/-- Every source label remains its same literal individual label. -/
@[simp]
theorem vertex_object (D : FixedObjects O) (s : A) : vertex (object a D) s = s := rfl

/-- Restriction keeps the Hom at both prescribed target labels. -/
theorem hom_object (D : FixedObjects O) (s t : A) :
    hom (object a D) s t = hom D (a s) (a t) := rfl

/-- The unit at the prescribed image is unchanged. -/
theorem identity_object (D : FixedObjects O) (s : A) :
    identityMap (object a D) s = identityMap D (a s) := rfl

/-- The composition uses the same three prescribed target labels. -/
theorem composition_object (D : FixedObjects O) (s t r : A) :
    compositionMap (object a D) s t r = compositionMap D (a s) (a t) (a r) := rfl

/-- Restriction acts on each same Hom map and proves its enriched laws. -/
def map {D E : FixedObjects O} (F : D ⟶ E) : object a D ⟶ object a E :=
  ofHomMaps (fun s t => homMap F (a s) (a t))
    (fun s => identityMap_homMap F (a s))
    (fun s t r => compositionMap_homMap F (a s) (a t) (a r))

/-- The restricted functor has the identical Hom map at every pair of labels. -/
@[simp]
theorem homMap_map {D E : FixedObjects O} (F : D ⟶ E) (s t : A) :
    homMap (map a F) s t = homMap F (a s) (a t) :=
  homMap_ofHomMaps _ _ _ s t

/-- The restricted functor fixes the same individual source label. -/
@[simp]
theorem map_obj {D E : FixedObjects O} (F : D ⟶ E) (s : A) :
    (map a F).val.obj s = s := by
  change vertex (object a E) (label (object a D) s) = s
  rw [← vertex_object a D s, label_vertex]
  rfl

/-- The restriction functor retains every enriched map and both ordinary
functor laws. -/
def functor : FixedObjects O ⥤ FixedObjects A where
  obj := object a
  map := map a
  map_id D := by
    apply homMaps_ext
    intro s t
    simp
    rfl
  map_comp F G := by
    apply homMaps_ext
    intro s t
    simp
    rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelRestriction

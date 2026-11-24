/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeQuiver

/-!
# The ordinary category of actual small simplicial enrichments

This carrier bundles an existing enrichment and uses genuine enriched
functors as its arrows. The ordinary composition is strictly associative;
the Hom categories and their noninvertible enriched transformations are
not collapsed or replaced by an assumed model structure.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment

/-- A bundled original object type with its actual simplicial enrichment. -/
structure Carrier where
  /-- The existing enriched category, with its original object type and Hom simplicial sets. -/
  toEnrichedCat : EnrichedCat.{u, u + 1, u} SSet.{u}

instance : CoeSort Carrier (Type u) := ⟨fun C => C.toEnrichedCat⟩
instance (C : Carrier) : EnrichedCategory SSet.{u} C := C.toEnrichedCat.str

/-- Bundle a supplied actual enrichment, preserving its original objects and all Hom simplices. -/
def of (C : Type u) [EnrichedCategory SSet.{u} C] : Carrier :=
  ⟨EnrichedCat.of SSet.{u} C⟩

instance : Category.{u} Carrier where
  Hom C D := EnrichedFunctor SSet.{u} C D
  id C := EnrichedFunctor.id SSet.{u} C
  comp F G := F.comp SSet.{u} G
  id_comp {C D} F := by
    refine EnrichedFunctor.ext SSet.{u}
      (F := (EnrichedFunctor.id SSet.{u} C).comp SSet.{u} F) (G := F) (fun _ => rfl) ?_
    intro x y
    change (𝟙 _ ≫ F.map x y) ≫ 𝟙 _ = F.map x y
    simp only [Category.id_comp, Category.comp_id]
  comp_id {C D} F := by
    refine EnrichedFunctor.ext SSet.{u}
      (F := F.comp SSet.{u} (EnrichedFunctor.id SSet.{u} D)) (G := F) (fun _ => rfl) ?_
    intro x y
    change (F.map x y ≫ 𝟙 _) ≫ 𝟙 _ = F.map x y
    simp only [Category.comp_id]
  assoc F G H := by
    refine EnrichedFunctor.ext SSet.{u}
      (F := (F.comp SSet.{u} G).comp SSet.{u} H)
      (G := F.comp SSet.{u} (G.comp SSet.{u} H)) (fun _ => rfl) ?_
    intro x y
    change ((F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫
      H.map (G.obj (F.obj x)) (G.obj (F.obj y))) ≫ 𝟙 _ =
        F.map x y ≫ (G.map (F.obj x) (F.obj y) ≫
          H.map (G.obj (F.obj x)) (G.obj (F.obj y)))
    simp only [Category.comp_id, Category.assoc]

/-- Ordinary composition is the same actual enriched composition on every original Hom map. -/
theorem comp_map {C D E : Carrier} (F : C ⟶ D) (G : D ⟶ E) (x y : C) :
    (F ≫ G).map x y = F.map x y ≫ G.map (F.obj x) (F.obj y) := rfl

end CategoryTheory.SimplicialEnrichment

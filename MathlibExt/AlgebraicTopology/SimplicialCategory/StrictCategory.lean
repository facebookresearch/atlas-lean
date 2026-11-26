/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeQuiver
import MathlibExt.AlgebraicTopology.CategoricalSource.EnrichedCat

/-!
# The ordinary category of actual small simplicial enrichments

The carrier specializes the existing `EnrichedCat` category to simplicial
enrichments and uses genuine enriched functors as its arrows. The ordinary
composition is strictly associative;
the Hom categories and their noninvertible enriched transformations are
not collapsed or replaced by an assumed model structure.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment

/-- A bundled original object type with its actual simplicial enrichment. -/
abbrev Carrier := EnrichedCat.{u, u + 1, u} SSet.{u}

/-- Regard an existing simplicial enriched category as a carrier. -/
abbrev Carrier.mk (C : EnrichedCat.{u, u + 1, u} SSet.{u}) : Carrier.{u} := C

/-- The existing enriched category, with its original object type and Hom simplicial sets. -/
abbrev Carrier.toEnrichedCat (C : Carrier.{u}) : EnrichedCat.{u, u + 1, u} SSet.{u} := C

/-- Bundle a supplied actual enrichment, preserving its original objects and all Hom simplices. -/
def of (C : Type u) [EnrichedCategory SSet.{u} C] : Carrier :=
  EnrichedCat.of SSet.{u} C

/-- Ordinary composition is the same actual enriched composition on every original Hom map. -/
theorem comp_map {C D E : Carrier} (F : C ⟶ D) (G : D ⟶ E) (x y : C) :
    (F ≫ G).map x y = F.map x y ≫ G.map (F.obj x) (F.obj y) := rfl

end CategoryTheory.SimplicialEnrichment

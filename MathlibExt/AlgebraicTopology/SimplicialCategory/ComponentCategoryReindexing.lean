/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.Reindexing
import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategory
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Groupoid

/-!
# The original component category under literal enrichment reindexing

The full projection has identity maps on the SAME original Hom
simplicial sets. Its component functor is genuinely fully faithful,
including duplicate or empty labels in an independent universe.
Original groupoid components therefore remain groupoid components.
-/

noncomputable section
universe u v w
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.ComponentCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C] {O : Type w}

/-- The SAME full reindexing projection induces the literal original component functor. -/
def reindexProjectionFunctor (a : O → C) :
    let _ : EnrichedCategory SSet.{u} O := EnrichedCategory.reindex SSet.{u} a
    objects.{u} O ⥤ objects.{u} C := by
  let _ : EnrichedCategory SSet.{u} O := EnrichedCategory.reindex SSet.{u} a
  exact mapFunctor (EnrichedCategory.reindexProjection SSet.{u} a)

/-- Every SAME original reindexed component Hom map is bijective,
without any injectivity premise on the object function. -/
def reindexProjectionFullyFaithful (a : O → C) :
    let _ : EnrichedCategory SSet.{u} O := EnrichedCategory.reindex SSet.{u} a
    (reindexProjectionFunctor a).FullyFaithful := by
  let _ : EnrichedCategory SSet.{u} O := EnrichedCategory.reindex SSet.{u} a
  apply Classical.choice
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
  intro x y
  change Function.Bijective (SSet.mapπ₀ (𝟙 (a x ⟶[SSet.{u}] a y)))
  have h : SSet.mapπ₀ (𝟙 (a x ⟶[SSet.{u}] a y)) = _root_.id :=
    funext SSet.mapπ₀_id_apply
  rw [h]
  exact Function.bijective_id

/-- Original groupoid components survive literal reindexing in any
independent label universe through the SAME fully faithful projection. -/
theorem reindex_isGroupoid (a : O → C) [IsGroupoid (objects.{u} C)] :
    let _ : EnrichedCategory SSet.{u} O := EnrichedCategory.reindex SSet.{u} a
    IsGroupoid (objects.{u} O) := by
  let _ : EnrichedCategory SSet.{u} O := EnrichedCategory.reindex SSet.{u} a
  let _ : (reindexProjectionFunctor a).ReflectsIsomorphisms :=
    (reindexProjectionFullyFaithful a).reflectsIsomorphisms
  exact isGroupoid_of_reflects_iso (reindexProjectionFunctor a)

end CategoryTheory.SimplicialEnrichment.ComponentCategory

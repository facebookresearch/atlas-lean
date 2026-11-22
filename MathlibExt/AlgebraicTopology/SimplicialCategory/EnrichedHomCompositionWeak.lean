/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomCompositionFamilies
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomFibrantReplacement
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FullProductWeakEquivalences

/-!
# Genuine weakness of the full original Hom composition graph

The SAME complete original composition graph is weak whenever the
original component category is a groupoid. No Kan condition on any
original Hom is assumed. The genuine original free-horn replacement,
its full weak Hom maps and the literal enriched graph square reduce
to the proved Kan-fibre comparison without changing the original map.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomCompositionFamilies

variable (C : Type u) [EnrichedCategory SSet.{u} C]

/-- The SAME entire original enriched composition graph is weak for
original groupoid components, with every original Hom and parameter retained. -/
theorem postGraph_weak [IsGroupoid (ComponentCategory.objects.{u} C)] (z x y : C) :
    SSet.realizationWeakEquivalences (postGraph z x y) := by
  let R := FixedObjectHomFibrantReplacement.map C
  let _ : SSet.KanComplex (R.obj z ⟶[SSet.{u}] R.obj x) :=
    FixedObjectHomFibrantReplacement.homKan C _ _
  let _ : SSet.KanComplex (R.obj z ⟶[SSet.{u}] R.obj y) :=
    FixedObjectHomFibrantReplacement.homKan C _ _
  let _ : SSet.KanComplex (R.obj x ⟶[SSet.{u}] R.obj y) :=
    FixedObjectHomFibrantReplacement.homKan C _ _
  let _ : IsGroupoid (ComponentCategory.objects.{u} (FixedObjectHomFibrantReplacement.object C)) :=
    FixedObjectHomFibrantReplacement.component_isGroupoid C
  have hR : ∀ a b : C, SSet.realizationWeakEquivalences (R.map a b) :=
    FixedObjectHomFibrantReplacement.map_hom_weak C
  have hRight := SSet.realizationWeakEquivalences.tensorHom (R.map z y) (R.map x y)
    (hR z y) (hR x y)
  have hLeft := SSet.realizationWeakEquivalences.tensorHom (R.map z x) (R.map x y)
    (hR z x) (hR x y)
  have hTarget := postGraph_weak_of_Kan (R.obj z) (R.obj x) (R.obj y)
  apply SSet.realizationWeakEquivalences.of_postcomp _ _ hRight
  rw [postGraph_natural R z x y]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hLeft hTarget

end CategoryTheory.SimplicialEnrichment.EnrichedHomCompositionFamilies

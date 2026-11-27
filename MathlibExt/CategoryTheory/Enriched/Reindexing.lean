/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Reindex the SAME original enrichment along an object function

Every Hom object, unit and composition is literally the original one
at the supplied images. The coefficient-object, coefficient-morphism,
original-object and label universes are independent. The full original
projection has the supplied object function and identity Hom maps.
-/

@[expose] public section

noncomputable section
universe uV vV uC uO uP
open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedCategory

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C] {O : Type uO}

/-- Reindex the SAME whole original enrichment on the supplied label type. -/
@[instance_reducible]
def reindex (a : O → C) : EnrichedCategory V O where
  Hom x y := a x ⟶[V] a y
  id x := eId V (a x)
  comp x y z := eComp V (a x) (a y) (a z)
  id_comp x y := e_id_comp V (a x) (a y)
  comp_id x y := e_comp_id V (a x) (a y)
  assoc w x y z := e_assoc V (a w) (a x) (a y) (a z)

/-- Every original reindexed Hom is literally the SAME original Hom object at the images. -/
lemma reindex_hom (a : O → C) (x y : O) :
    let _ : EnrichedCategory V O := reindex V a
    (x ⟶[V] y) = (a x ⟶[V] a y) := rfl

/-- Every reindexed unit is the SAME entire original unit. -/
lemma reindex_id (a : O → C) (x : O) :
    let _ : EnrichedCategory V O := reindex V a
    eId V x = eId V (a x) := rfl

/-- Every reindexed composition is the SAME complete original composition. -/
lemma reindex_comp (a : O → C) (x y z : O) :
    let _ : EnrichedCategory V O := reindex V a
    eComp V x y z = eComp V (a x) (a y) (a z) := rfl

/-- The full original projection retains the actual supplied object
function and the identity map on every SAME full Hom object. -/
def reindexProjection (a : O → C) :
    let _ : EnrichedCategory V O := reindex V a
    EnrichedFunctor V O C := by
  let _ : EnrichedCategory V O := reindex V a
  exact {
    obj := a
    map _ _ := 𝟙 _
    map_id _ := Category.comp_id _
    map_comp x y z := by
      change eComp V (a x) (a y) (a z) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp V (a x) (a y) (a z)
      simp only [Category.comp_id, id_tensorHom_id, Category.id_comp] }

/-- Its object map is the SAME literal supplied function. -/
lemma reindexProjection_obj (a : O → C) (x : O) :
    let _ : EnrichedCategory V O := reindex V a
    (reindexProjection V a).obj x = a x := rfl

/-- Its full original Hom map is literally the SAME original identity. -/
lemma reindexProjection_map (a : O → C) (x y : O) :
    let _ : EnrichedCategory V O := reindex V a
    (reindexProjection V a).map x y = 𝟙 (a x ⟶[V] a y) := rfl

/-- Successive reindexing retains the SAME whole original enrichment
of the composite object function, in independent label universes. -/
lemma reindex_reindex (a : O → C) {P : Type uP} (b : P → O) :
    (let _ : EnrichedCategory V O := reindex V a; reindex V b) = reindex V (a ∘ b) := rfl

/-- Reindexing along the identity retains the SAME complete original enrichment. -/
lemma reindex_identity :
    reindex V (_root_.id : C → C) = (inferInstance : EnrichedCategory V C) := rfl

end CategoryTheory.EnrichedCategory

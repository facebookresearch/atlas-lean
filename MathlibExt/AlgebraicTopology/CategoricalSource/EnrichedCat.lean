/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
module

/-
Completed proof port; original Apache 2.0 author/license header retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Enriched/EnrichedCat.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only import paths and the TauCeti helper namespace are adapted.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.Enriched.EnrichedCat

/-!
# The category of enriched categories

Mathlib's `EnrichedCat V` is the bicategory of `V`-enriched categories, `V`-functors and
enriched natural transformations. Composition of `V`-functors is strictly unital and associative,
so this bicategory is strict, and its underlying ordinary category has the `V`-enriched categories
as objects and the `V`-functors as morphisms. For `V = SSet` this is the category of simplicial
categories and simplicial functors on which the homotopy coherent nerve is a functor.

## Main declarations

* `CategoryTheory.EnrichedCat.bicategory.strict`: the bicategory `EnrichedCat V` is strict.
* `CategoryTheory.EnrichedCat.category`: the category of `V`-enriched categories and
  `V`-functors.
-/

public section

universe w v u u₁ u₂ u₃ u₄

namespace CategoryTheory

namespace EnrichedFunctor

variable {V : Type v} [Category.{w} V] [MonoidalCategory V] {C : Type u₁} {D : Type u₂}
  {E : Type u₃} {F : Type u₄} [EnrichedCategory V C] [EnrichedCategory V D]
  [EnrichedCategory V E] [EnrichedCategory V F]

@[simp]
lemma id_comp (G : EnrichedFunctor V C D) : (EnrichedFunctor.id V C).comp V G = G := by
  obtain ⟨obj, map, _, _⟩ := G
  simp only [EnrichedFunctor.comp, EnrichedFunctor.id, Category.id_comp]

@[simp]
lemma comp_id (G : EnrichedFunctor V C D) : G.comp V (EnrichedFunctor.id V D) = G := by
  obtain ⟨obj, map, _, _⟩ := G
  simp only [EnrichedFunctor.comp, EnrichedFunctor.id, Category.comp_id]

lemma comp_assoc (G : EnrichedFunctor V C D) (H : EnrichedFunctor V D E)
    (K : EnrichedFunctor V E F) : (G.comp V H).comp V K = G.comp V (H.comp V K) := by
  simp only [EnrichedFunctor.comp, Category.assoc]

/-- Enriched natural transformations are determined by their underlying natural
transformations. -/
lemma hom_ext_of_out_eq {G H : EnrichedFunctor V C D} {α β : G ⟶ H} (h : α.out = β.out) :
    α = β := by
  cases α
  cases β
  cases h
  rfl

/-- The enriched natural transformation given by an equality of `V`-functors has identity
components after forgetting the enrichment. -/
lemma eqToHom_out_app {G H : EnrichedFunctor V C D} (h : G = H) (X : ForgetEnrichment V C) :
    (eqToHom h).out.app X = eqToHom (by rw [h]) := by
  subst h
  rfl

end EnrichedFunctor

namespace EnrichedCat

variable {V : Type v} [Category.{w} V] [MonoidalCategory V] {C D E F : Type u}
  [EnrichedCategory V C] [EnrichedCategory V D] [EnrichedCategory V E] [EnrichedCategory V F]

/-- The left unitor of `EnrichedCat V` is the identity. -/
lemma leftUnitor_eq_eqToIso (G : EnrichedFunctor V C D) :
    leftUnitor G = eqToIso (EnrichedFunctor.id_comp G) := by
  refine Iso.ext (EnrichedFunctor.hom_ext_of_out_eq (NatTrans.ext (funext fun X ↦ ?_)))
  rw [eqToIso.hom, EnrichedFunctor.eqToHom_out_app]
  simp only [EnrichedFunctor.forget_obj, leftUnitor_hom_out_app]
  exact (eqToHom_refl (C := ForgetEnrichment V D) _ _).symm

/-- The right unitor of `EnrichedCat V` is the identity. -/
lemma rightUnitor_eq_eqToIso (G : EnrichedFunctor V C D) :
    rightUnitor G = eqToIso (EnrichedFunctor.comp_id G) := by
  refine Iso.ext (EnrichedFunctor.hom_ext_of_out_eq (NatTrans.ext (funext fun X ↦ ?_)))
  rw [eqToIso.hom, EnrichedFunctor.eqToHom_out_app]
  simp only [EnrichedFunctor.forget_obj, rightUnitor_hom_out_app]
  exact (eqToHom_refl (C := ForgetEnrichment V D) _ _).symm

/-- The associator of `EnrichedCat V` is the identity. -/
lemma associator_eq_eqToIso (G : EnrichedFunctor V C D) (H : EnrichedFunctor V D E)
    (K : EnrichedFunctor V E F) :
    associator G H K = eqToIso (EnrichedFunctor.comp_assoc G H K) := by
  refine Iso.ext (EnrichedFunctor.hom_ext_of_out_eq (NatTrans.ext (funext fun X ↦ ?_)))
  rw [eqToIso.hom, EnrichedFunctor.eqToHom_out_app]
  simp only [EnrichedFunctor.forget_obj, associator_hom_out_app]
  exact (eqToHom_refl (C := ForgetEnrichment V F) _ _).symm

variable (V)

/-- The bicategory of `V`-enriched categories is strict: composition of `V`-functors is unital
and associative on the nose. -/
instance bicategory.strict : Bicategory.Strict (EnrichedCat.{w, v, u} V) where
  id_comp := EnrichedFunctor.id_comp
  comp_id := EnrichedFunctor.comp_id
  assoc := EnrichedFunctor.comp_assoc
  leftUnitor_eqToIso := leftUnitor_eq_eqToIso
  rightUnitor_eqToIso := rightUnitor_eq_eqToIso
  associator_eqToIso := associator_eq_eqToIso

/-- The category of `V`-enriched categories, with `V`-functors as morphisms. -/
instance category : Category (EnrichedCat.{w, v, u} V) :=
  StrictBicategory.category (EnrichedCat.{w, v, u} V)

variable {V}

@[simp]
lemma id_eq (C : EnrichedCat.{w, v, u} V) : 𝟙 C = EnrichedFunctor.id V C :=
  rfl

@[simp]
lemma comp_eq {C D E : EnrichedCat.{w, v, u} V} (F : C ⟶ D) (G : D ⟶ E) :
    F ≫ G = F.comp V G :=
  rfl

end EnrichedCat

end CategoryTheory

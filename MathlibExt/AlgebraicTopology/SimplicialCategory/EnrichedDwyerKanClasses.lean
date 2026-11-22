/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategory
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModelClasses
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Equivalence

/-!
# Actual changing-object enriched Dwyer–Kan weak classes

The weak predicate uses every original Hom map and actual essential
surjectivity of the same ordinary component functor. Only Hom sets use
components; original objects remain individual. Local scalar weakness
constructs genuine full faithfulness. No changing-object model structure
or nerve equivalence is an input to these definitions or comparisons.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.EnrichedDwyerKan

variable {C D E : Carrier.{u}}

/-- The actual original scalar Hom weak predicate, without changing any original endpoint. -/
def localWeak (F : C ⟶ D) : Prop := ∀ x y : C, SSet.realizationWeakEquivalences (F.map x y)

/-- The actual changing-object enriched weak class on the original strict carrier. -/
def weakEquivalences : MorphismProperty Carrier.{u} :=
  fun _ _ F => localWeak F ∧ (ComponentCategory.mapFunctor F).EssSurj

/-- Actual scalar Hom weakness constructs full faithfulness of the same original component functor. -/
def componentFullyFaithful (F : C ⟶ D) (hF : localWeak F) :
    (ComponentCategory.mapFunctor F).FullyFaithful :=
  Classical.choice ((Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
    (fun x y => (hF x y).bijective_mapπ₀))

/-- A genuine enriched weak map induces an ordinary component-category equivalence on its same original objects. -/
theorem componentIsEquivalence (F : C ⟶ D) (hF : weakEquivalences F) :
    (ComponentCategory.mapFunctor F).IsEquivalence := {
  faithful := (componentFullyFaithful F hF.1).faithful
  full := (componentFullyFaithful F hF.1).full
  essSurj := hF.2 }

/-- A whole component-category equivalence with the supplied original forward functor and both inverse comparisons. -/
def componentEquivalence (F : C ⟶ D) (hF : weakEquivalences F) :
    ComponentCategory.objects.{u} C ≌ ComponentCategory.objects.{u} D := by
  let _ := componentIsEquivalence F hF
  exact (ComponentCategory.mapFunctor F).asEquivalence

/-- The genuine ordinary comparison's forward functor is the same actual component functor. -/
theorem componentEquivalence_functor (F : C ⟶ D) (hF : weakEquivalences F) :
    (componentEquivalence F hF).functor = ComponentCategory.mapFunctor F := rfl

/-- Local weakness composes on every whole original Hom map. -/
theorem localWeak_comp (F : C ⟶ D) (G : D ⟶ E) (hF : localWeak F) (hG : localWeak G) :
    localWeak (F ≫ G) := by
  intro x y
  exact SSet.realizationWeakEquivalences.comp_mem _ _ (hF x y) (hG (F.obj x) (F.obj y))

/-- The actual original enriched identity is a genuine Dwyer–Kan weak map. -/
theorem identity_weak (C : Carrier.{u}) : weakEquivalences (𝟙 C) := by
  constructor
  · intro x y
    exact SSet.realizationWeakEquivalences.id_mem _
  · change (ComponentCategory.mapFunctor (EnrichedFunctor.id SSet.{u} C)).EssSurj
    rw [ComponentCategory.mapFunctor_id]
    infer_instance

/-- Genuine enriched weak maps compose using actual local weakness and the same component equivalence. -/
theorem comp_weak (F : C ⟶ D) (G : D ⟶ E) (hF : weakEquivalences F) (hG : weakEquivalences G) :
    weakEquivalences (F ≫ G) := by
  refine ⟨localWeak_comp F G hF.1 hG.1, ?_⟩
  let _ := componentIsEquivalence F hF
  let _ := componentIsEquivalence G hG
  change (ComponentCategory.mapFunctor (EnrichedFunctor.comp SSet.{u} F G)).EssSurj
  rw [ComponentCategory.mapFunctor_comp]
  infer_instance

/-- The changing-object Dwyer–Kan class contains every original identity. -/
instance weak_containsIdentities : weakEquivalences.{u}.ContainsIdentities where
  id_mem := identity_weak

/-- The changing-object Dwyer–Kan class is closed under actual composition. -/
instance weak_stableUnderComposition : weakEquivalences.{u}.IsStableUnderComposition where
  comp_mem := comp_weak

/-- Identities and composition give the standard multiplicative morphism property. -/
instance weak_multiplicative : weakEquivalences.{u}.IsMultiplicative := ⟨⟩

/-- On the actual fixed-object fiber this weak class agrees exactly with the proved original KQ model weak class. -/
theorem fixedWeak_iff {O : Type u} {A B : FixedObjects O} (F : A ⟶ B) :
    weakEquivalences F.val ↔ FixedObjects.FixedObjectModel.weakEquivalences O F := by
  constructor
  · intro hF
    exact (FixedObjects.FixedObjectModel.weakEquivalences_original_iff F).mpr hF.1
  · intro hF
    refine ⟨(FixedObjects.FixedObjectModel.weakEquivalences_original_iff F).mp hF, ?_⟩
    exact Functor.essSurj_of_surj (FixedObjects.objects_bijective F).surjective

end CategoryTheory.SimplicialEnrichment.EnrichedDwyerKan

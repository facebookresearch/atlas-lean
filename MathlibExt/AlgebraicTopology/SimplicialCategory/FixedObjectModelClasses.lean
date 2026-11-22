/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingSmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# The five actual fixed-object simplicial-category classes

Weak equivalences are tested on each whole original Hom simplicial set.
The actual literal free horn and boundary right lifting classes detect
the scalar fibration and trivial-fibration classes. The two genuine
small-object constructions supply their weak factorization systems.
The remaining model acyclicity uses the actual word-filtration theorem.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel

variable (O : Type u)

/-- Actual scalar weak equivalences on every original fixed-label Hom object. -/
def weakEquivalences : MorphismProperty (FixedObjects O) :=
  ⨅ x : O, ⨅ y : O, SSet.realizationWeakEquivalences.inverseImage (evaluation x y)

/-- The actual literal free-horn right lifting class. -/
abbrev fibrations : MorphismProperty (FixedObjects O) := (hornFamily O).rlp

/-- The actual free-boundary left lifting class. -/
abbrev cofibrations : MorphismProperty (FixedObjects O) := (boundaryFamily O).rlp.llp

/-- The actual literal free-boundary right lifting class. -/
abbrev trivialFibrations : MorphismProperty (FixedObjects O) := (boundaryFamily O).rlp

/-- The actual free-horn left lifting class, with acyclicity proved by the original word filtration. -/
abbrev trivialCofibrations : MorphismProperty (FixedObjects O) := (hornFamily O).rlp.llp

variable {O}

/-- Weak membership tests the same entire original Hom maps at every original label pair. -/
theorem weakEquivalences_iff {C D : FixedObjects O} (f : C ⟶ D) :
    weakEquivalences O f ↔ ∀ x y : O, SSet.realizationWeakEquivalences (homMap f x y) := by
  simp only [weakEquivalences, MorphismProperty.iInf_iff]
  rfl

/-- The weak class retains every individual original source vertex and whole Hom map. -/
theorem weakEquivalences_original_iff {C D : FixedObjects O} (f : C ⟶ D) :
    weakEquivalences O f ↔ ∀ a b : C.val, SSet.realizationWeakEquivalences (f.val.map a b) :=
  (weakEquivalences_iff f).trans (all_homMap_property_iff SSet.realizationWeakEquivalences f)

/-- Fibration membership is genuine scalar Kan fibration at every whole original Hom. -/
theorem fibrations_iff {C D : FixedObjects O} (f : C ⟶ D) :
    fibrations O f ↔ ∀ x y : O, Fibration (homMap f x y) := by
  rw [fibrations, hornFamily_rlp_eq]
  exact hornGenerators_rlp_iff f

/-- The actual free-boundary class is precisely scalar trivial fibration on every original Hom. -/
theorem trivialFibrations_iff {C D : FixedObjects O} (f : C ⟶ D) :
    trivialFibrations O f ↔ ∀ x y : O,
      Fibration (homMap f x y) ∧ SSet.realizationWeakEquivalences (homMap f x y) := by
  rw [trivialFibrations, boundaryFamily_rlp_eq]
  exact boundaryGenerators_rlp_iff f

/-- The actual trivial-fibration class is exactly the intersection of the actual fibration and weak classes. -/
theorem trivialFibrations_eq : trivialFibrations O = fibrations O ⊓ weakEquivalences O := by
  ext C D f
  change trivialFibrations O f ↔ fibrations O f ∧ weakEquivalences O f
  rw [trivialFibrations_iff, fibrations_iff, weakEquivalences_iff]
  exact ⟨fun h => ⟨fun x y => (h x y).1, fun x y => (h x y).2⟩,
    fun h x y => ⟨h.1 x y, h.2 x y⟩⟩

/-- Every genuine free-boundary right map is in the same free-horn right class. -/
theorem trivialFibrations_le_fibrations : trivialFibrations O ≤ fibrations O := by
  rw [trivialFibrations_eq]
  exact inf_le_left

/-- The actual free-horn left maps lie in the actual free-boundary left class. -/
theorem trivialCofibrations_le_cofibrations : trivialCofibrations O ≤ cofibrations O :=
  MorphismProperty.antitone_llp trivialFibrations_le_fibrations

instance weak_respectsIso : (weakEquivalences O).RespectsIso := by
  dsimp only [weakEquivalences]
  infer_instance

instance weak_twoOutOfThree : (weakEquivalences O).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := by
    rw [weakEquivalences_iff] at hf hg ⊢
    intro x y
    rw [homMap_comp]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ (hf x y) (hg x y)
  of_postcomp f g hg hfg := by
    rw [weakEquivalences_iff] at hg hfg ⊢
    intro x y
    exact SSet.realizationWeakEquivalences.of_postcomp _ _ (hg x y)
      (by rw [← homMap_comp]; exact hfg x y)
  of_precomp f g hf hfg := by
    rw [weakEquivalences_iff] at hf hfg ⊢
    intro x y
    exact SSet.realizationWeakEquivalences.of_precomp _ _ (hf x y)
      (by rw [← homMap_comp]; exact hfg x y)

instance weak_containsIdentities : (weakEquivalences O).ContainsIdentities where
  id_mem C := by
    rw [weakEquivalences_iff]
    intro x y
    rw [homMap_id]
    exact (weakEquivalence_iff _).mp (inferInstance : WeakEquivalence (𝟙 (hom C x y)))

instance weak_multiplicative : (weakEquivalences O).IsMultiplicative := ⟨⟩

instance weak_retracts : (weakEquivalences O).IsStableUnderRetracts where
  of_retract h hg := by
    rw [weakEquivalences_iff] at hg ⊢
    intro x y
    exact MorphismProperty.of_retract (P := SSet.realizationWeakEquivalences) (h.map (evaluation x y)) (hg x y)

instance boundaryWFS : MorphismProperty.IsWeakFactorizationSystem (cofibrations O) (trivialFibrations O) :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun _i p hi hp => hi p hp)

instance hornWFS : MorphismProperty.IsWeakFactorizationSystem (trivialCofibrations O) (fibrations O) :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun _i p hi hp => hi p hp)

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel

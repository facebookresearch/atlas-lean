/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorObject
import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# Composition and whole-object currying for original one-fold functors

The fixed closed structure is used locally. Composition uses the same actual
evaluation transposes and the displayed product symmetry. The existing closed
enrichment and its opposite supply both identity laws and associativity.
-/

noncomputable section
universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonoidalCategory

namespace SimplicialPresheaf.OrderedJFS.OneFunctor

attribute [local instance] closed

private local instance : EnrichedCategory (Original.{u} 1) (Original.{u} 1) :=
  MonoidalClosed.enrichedCategorySelf _

/-- The identity point is the original identity's Cartesian transpose. -/
def identity (A : Original.{u} 1) : 𝟙_ (Original.{u} 1) ⟶ object A A :=
  MonoidalClosed.id A

/-- Composition first takes the later functor and then the earlier functor. -/
def composition (A B C : Original.{u} 1) :
    object B C ⊗ object A B ⟶ object A C :=
  (β_ (object B C) (object A B)).hom ≫ MonoidalClosed.comp A B C

/-- This composition is exactly the transpose of the two original evaluations. -/
theorem uncurry_composition (A B C : Original.{u} 1) :
    uncurry (composition A B C) =
      A ◁ (β_ (object B C) (object A B)).hom ≫
        (α_ A (object A B) (object B C)).inv ≫
          evaluation A B ▷ object B C ≫ evaluation B C := by
  change MonoidalClosed.uncurry
      ((β_ _ _).hom ≫ MonoidalClosed.comp A B C) = _
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.comp_eq,
    MonoidalClosed.uncurry_curry]
  rfl

/-- The later identity leaves the original full functor object fixed. -/
@[reassoc] theorem composition_left_identity (A B : Original.{u} 1) :
    (λ_ (object A B)).inv ≫ identity B ▷ object A B ≫ composition A B B = 𝟙 _ :=
  EnrichedCategory.id_comp (V := Original.{u} 1) (op B) (op A)

/-- The earlier identity leaves the original full functor object fixed. -/
@[reassoc] theorem composition_right_identity (A B : Original.{u} 1) :
    (ρ_ (object A B)).inv ≫ object A B ◁ identity A ≫ composition A A B = 𝟙 _ :=
  EnrichedCategory.comp_id (V := Original.{u} 1) (op B) (op A)

/-- Three actual functors compose associatively with the original product associator. -/
@[reassoc] theorem composition_assoc (A B C D : Original.{u} 1) :
    (α_ (object C D) (object B C) (object A B)).inv ≫
        composition B C D ▷ object A B ≫ composition A B D =
      object C D ◁ composition A B C ≫ composition A C D :=
  EnrichedCategory.assoc (V := Original.{u} 1) (op D) (op C) (op B) (op A)

/-- The exponential law is an isomorphism of entire original one-fold objects. -/
def curryingIso (A B C : Original.{u} 1) :
    object (A ⊗ B) C ≅ object A (object B C) :=
  (MonoidalClosed.internalHom.mapIso (β_ B A).op).app C ≪≫
    MonoidalClosed.ihomCurryIso B A C

/-- Both Cartesian transposes are the same original evaluation under its associator and symmetry. -/
theorem curryingIso_evaluation (A B C : Original.{u} 1) :
    uncurry (uncurry (curryingIso A B C).hom) =
      (α_ B A (object (A ⊗ B) C)).inv ≫
        (β_ B A).hom ▷ object (A ⊗ B) C ≫ evaluation (A ⊗ B) C := by
  change MonoidalClosed.uncurry (MonoidalClosed.uncurry
    ((MonoidalClosed.pre (β_ B A).hom).app C ≫ MonoidalClosed.ihomCurry B A C)) = _
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_uncurry_ihomCurry, associator_inv_naturality_right_assoc,
    MonoidalClosed.id_tensor_pre_app_comp_ev]
  rfl

/-- Whole-object currying is natural in the original target map. -/
@[reassoc] theorem curryingIso_target (A B : Original.{u} 1)
    {C D : Original.{u} 1} (g : C ⟶ D) :
    targetMap (A ⊗ B) g ≫ (curryingIso A B D).hom =
      (curryingIso A B C).hom ≫ targetMap A (targetMap B g) := by
  apply ((adjunction A).homEquiv _ _).symm.injective
  apply ((adjunction B).homEquiv _ _).symm.injective
  change uncurry (uncurry (_ ≫ _)) = uncurry (uncurry (_ ≫ _))
  rw [uncurry_natural_left, uncurry_natural_left,
    uncurry_natural_right, uncurry_natural_right]
  rw [curryingIso_evaluation, curryingIso_evaluation,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    evaluation_target]
  simp only [Category.assoc]

/-- Whole-object currying retains contravariance in the first original source. -/
@[reassoc] theorem curryingIso_source_left {A A' : Original.{u} 1}
    (f : A ⟶ A') (B C : Original.{u} 1) :
    sourceMap (f ⊗ₘ 𝟙 B) C ≫ (curryingIso A B C).hom =
      (curryingIso A' B C).hom ≫ sourceMap f (object B C) := by
  apply ((adjunction A).homEquiv _ _).symm.injective
  apply ((adjunction B).homEquiv _ _).symm.injective
  change uncurry (uncurry (_ ≫ _)) = uncurry (uncurry (_ ≫ _))
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_source, uncurry_natural_left,
    curryingIso_evaluation, curryingIso_evaluation,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    evaluation_source, tensorHom_id, associator_inv_naturality_middle_assoc]
  simp only [← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_right]

/-- Whole-object currying retains contravariance in the second original source. -/
@[reassoc] theorem curryingIso_source_right (A : Original.{u} 1)
    {B B' : Original.{u} 1} (f : B ⟶ B') (C : Original.{u} 1) :
    sourceMap (𝟙 A ⊗ₘ f) C ≫ (curryingIso A B C).hom =
      (curryingIso A B' C).hom ≫ targetMap A (sourceMap f C) := by
  apply ((adjunction A).homEquiv _ _).symm.injective
  apply ((adjunction B).homEquiv _ _).symm.injective
  change uncurry (uncurry (_ ≫ _)) = uncurry (uncurry (_ ≫ _))
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_natural_right, uncurry_source,
    curryingIso_evaluation, curryingIso_evaluation,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    evaluation_source, id_tensorHom, associator_inv_naturality_left_assoc]
  simp only [← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left]

end SimplicialPresheaf.OrderedJFS.OneFunctor

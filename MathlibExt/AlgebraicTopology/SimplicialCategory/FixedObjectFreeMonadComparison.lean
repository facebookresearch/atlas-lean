/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeMonadAlgebra

/-!
# The actual original enriched and free-path algebra comparison

Every original simplicial enrichment gives its whole path algebra through
the canonical adjunction. Conversely, the two actual algebra equations
construct every enriched identity, composition and full Hom map. The
comparison preserves original labels and whole Hom families in both directions.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree

variable {O : Type u}

/-- The actual native monad comparison of the canonical original free/Hom adjunction. -/
def comparison : FixedObjects O ⥤ (pathMonad O).Algebra :=
  Monad.comparison (adjunction.{u} (O := O))

/-- The native comparison retains the entire original Hom family. -/
theorem comparison_family (C : FixedObjects O) :
    (comparison.obj C).A = (underlyingFunctor.{u} (O := O)).obj C := rfl

/-- The native comparison retains the complete original Hom map at both supplied endpoints. -/
theorem comparison_map {C D : FixedObjects O} (f : C ⟶ D) (x y : O) :
    (comparison.map f).f (x, y) = homMap f x y := rfl

/-- The comparison action is the same original whole path evaluation. -/
theorem comparison_action (C : FixedObjects O) (x y : O) :
    action (comparison.obj C) x y = homMap (evaluate C) x y := rfl

variable {A B : (pathMonad O).Algebra}

/-- Every algebra morphism retains the whole original path action equation. -/
theorem action_hom (f : A ⟶ B) (x y : O) :
    action A x y ≫ f.f (x, y) =
      homMap (FreeQuiver.map (Q := quiver A.A) (R := quiver B.A)
        (fun a b => f.f (a, b))) x y ≫ action B x y :=
  (congrArg (fun k => k (x, y)) f.h).symm

/-- The actual original algebra morphism preserves the constructed enriched identities. -/
theorem identity_hom (f : A ⟶ B) (x : O) :
    algebraIdentity A x ≫ f.f (x, x) = algebraIdentity B x := by
  unfold algebraIdentity
  erw [Category.assoc, action_hom, ← Category.assoc]

/-- The actual original algebra morphism preserves the full binary composition map. -/
theorem composition_hom (f : A ⟶ B) (x y z : O) :
    algebraComposition A x y z ≫ f.f (x, z) =
      (f.f (x, y) ⊗ₘ f.f (y, z)) ≫ algebraComposition B x y z := by
  unfold algebraComposition
  erw [Category.assoc, action_hom, ← Category.assoc, pairWord_map, Category.assoc]

/-- Actual algebra morphisms construct the same whole identity- and composition-preserving
enriched maps. -/
def algebraMap (f : A ⟶ B) : ofAlgebra A ⟶ ofAlgebra B :=
  ofHomMaps (fun x y => f.f (x, y)) (identity_hom f) (composition_hom f)

/-- The enriched algebra map retains each entire original supplied Hom map. -/
theorem homMap_algebraMap (f : A ⟶ B) (x y : O) :
    homMap (algebraMap f) x y = f.f (x, y) := homMap_ofHomMaps _ _ _ x y

/-- The actual construction from algebras is functorial on all original full Hom maps. -/
def realization : (pathMonad O).Algebra ⥤ FixedObjects O where
  obj A := ofAlgebra A
  map f := algebraMap f
  map_id A := by
    apply homMaps_ext
    intro x y
    rw [homMap_algebraMap, homMap_id]
    rfl
  map_comp f g := by
    apply homMaps_ext
    intro x y
    rw [homMap_algebraMap, homMap_comp, homMap_algebraMap, homMap_algebraMap]
    rfl

/-- Constructing and then reading the original algebra action returns that entire path map. -/
theorem evaluate_ofAlgebra (A : (pathMonad O).Algebra) :
    evaluate (ofAlgebra A) = actionMap A := by
  apply FreeQuiver.generators_ext
  intro x y
  erw [generator_evaluate, homMap_ofHomMaps]
  exact (generator_action A x y).symm

/-- Reading an original category through its actual algebra returns the full original
identity map. -/
theorem comparison_identity (C : FixedObjects O) (x : O) :
    algebraIdentity (comparison.obj C) x = identityMap C x :=
  identityMap_homMap (evaluate C) x

/-- Reading an original category through its actual algebra returns the full original
composition map. -/
theorem comparison_composition (C : FixedObjects O) (x y z : O) :
    algebraComposition (comparison.obj C) x y z = compositionMap C x y z :=
  pairWord_evaluate C x y z

/-- The comparison counit is the whole original fixed-object map, with identity on every
original Hom. -/
def originalMap (C : FixedObjects O) : ofAlgebra (comparison.obj C) ⟶ C :=
  ofHomMaps (fun x y => 𝟙 (hom C x y))
    (fun x => (Category.comp_id _).trans (comparison_identity C x))
    (fun x y z => by
      change algebraComposition (comparison.obj C) x y z = compositionMap C x y z
      exact comparison_composition C x y z)

/-- The inverse comparison map retains the same complete original Hom maps and original labels. -/
def originalInverse (C : FixedObjects O) : C ⟶ ofAlgebra (comparison.obj C) :=
  ofHomMaps (fun x y => 𝟙 (hom C x y))
    (fun x => (Category.comp_id _).trans (comparison_identity C x).symm)
    (fun x y z => by
      change compositionMap C x y z = algebraComposition (comparison.obj C) x y z
      exact (comparison_composition C x y z).symm)

/-- The forward original comparison map is the identity on every complete original Hom. -/
theorem homMap_originalMap (C : FixedObjects O) (x y : O) :
    homMap (originalMap C) x y = 𝟙 (hom C x y) := homMap_ofHomMaps _ _ _ x y

/-- The inverse original comparison map is the identity on the same complete original Hom. -/
theorem homMap_originalInverse (C : FixedObjects O) (x y : O) :
    homMap (originalInverse C) x y = 𝟙 (hom C x y) := homMap_ofHomMaps _ _ _ x y

/-- The actual comparison and reconstruction preserve the whole original enriched category
in both directions. -/
def originalIso (C : FixedObjects O) : ofAlgebra (comparison.obj C) ≅ C where
  hom := originalMap C
  inv := originalInverse C
  hom_inv_id := by
    apply homMaps_ext
    intro x y
    erw [homMap_comp, homMap_originalMap, homMap_originalInverse]
    exact Category.id_comp _
  inv_hom_id := by
    apply homMaps_ext
    intro x y
    erw [homMap_comp, homMap_originalInverse, homMap_originalMap]
    exact Category.id_comp _

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree

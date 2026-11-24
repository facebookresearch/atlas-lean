/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeSingleHomAdjunction
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Actual free single-Hom lifting classification

The genuine free/evaluation adjunction identifies full fixed-object
lifting problems with the corresponding scalar Hom lifting problems.
This supplies generator recognition without assuming a model structure
on enriched categories.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- The actual free images of the scalar generating maps at every original ordered pair. -/
def freeGenerators (P : MorphismProperty SSet.{u}) : MorphismProperty (FixedObjects O) :=
  ⨆ x : O, ⨆ y : O, P.map (FreeSingleHom.functor x y)

/-- An actual free-generator lifting problem is the corresponding original Hom lifting problem. -/
theorem hasLiftingProperty_free_iff (x y : O) {A B : SSet.{u}} (i : A ⟶ B)
    {C D : FixedObjects O} (p : C ⟶ D) :
    HasLiftingProperty ((FreeSingleHom.functor x y).map i) p ↔
      HasLiftingProperty i (homMap p x y) :=
  (FreeSingleHom.adjunction x y).hasLiftingProperty_iff i p

/-- Right lifting against all actual free generators is exactly right lifting on every
original Hom. -/
theorem freeGenerators_rlp_iff (P : MorphismProperty SSet.{u})
    {C D : FixedObjects O} (p : C ⟶ D) :
    (freeGenerators P).rlp p ↔ ∀ x y : O, P.rlp (homMap p x y) := by
  constructor
  · intro h x y A B i hi
    apply (hasLiftingProperty_free_iff x y i p).mp
    exact h _ ((MorphismProperty.iSup_iff _ _).mpr ⟨x,
      (MorphismProperty.iSup_iff _ _).mpr ⟨y,
        MorphismProperty.map_mem_map P (FreeSingleHom.functor x y) i hi⟩⟩)
  · intro h A B i hi
    obtain ⟨x, hi⟩ := (MorphismProperty.iSup_iff _ _).mp hi
    obtain ⟨y, X, Y, j, hj, ⟨e⟩⟩ := (MorphismProperty.iSup_iff _ _).mp hi
    have : HasLiftingProperty ((FreeSingleHom.functor x y).map j) p :=
      (hasLiftingProperty_free_iff x y j p).mpr (h x y j hj)
    exact HasLiftingProperty.of_arrow_iso_left e p

/-- The actual scalar lift equivalence keeps the whole fixed-object source and target equations. -/
def freeLiftEquiv (x y : O) {A B : SSet.{u}} {C D : FixedObjects O}
    {i : A ⟶ B} {p : C ⟶ D} {f : (FreeSingleHom.functor x y).obj A ⟶ C}
    {g : (FreeSingleHom.functor x y).obj B ⟶ D} (sq : CommSq f ((FreeSingleHom.functor x
      y).map i) p g) :
    sq.LiftStruct ≃ (sq.right_adjoint (FreeSingleHom.adjunction x y)).LiftStruct :=
  sq.rightAdjointLiftStructEquiv (FreeSingleHom.adjunction x y)

end CategoryTheory.SimplicialEnrichment.FixedObjects

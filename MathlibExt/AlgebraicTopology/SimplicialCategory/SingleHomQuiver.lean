/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeUniversalProperty
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# One supplied simplicial Hom among fixed original labels

The only noninitial generating Hom is at the supplied ordered pair. The
labels may coincide: a loop is still an original generator, and the free
category retains all its finite words.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.SimplicialQuiver.SingleHom

variable {O : Type u} (x y : O)

/-- Put the supplied simplicial set at exactly the given ordered pair of original labels. -/
def quiver (X : SSet.{u}) : Data O := by
  classical
  exact ⟨fun a b => if a = x ∧ b = y then X else ⊥_ SSet.{u}⟩

/-- The specified generating Hom is the literal supplied simplicial set. -/
@[simp]
theorem quiver_at (X : SSet.{u}) : (quiver x y X).Hom x y = X := by
  classical
  simp [quiver]

/-- All other ordered pairs have the actual initial generating Hom. -/
theorem quiver_other (X : SSet.{u}) (a b : O) (h : ¬(a = x ∧ b = y)) :
    (quiver x y X).Hom a b = ⊥_ SSet.{u} := by
  classical
  simp [quiver, h]

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- Extend a supplied Hom map to the whole generating family at the fixed object function. -/
def maps (X : SSet.{u}) (obj : O → C) (f : X ⟶ obj x ⟶[SSet.{u}] obj y)
    (a b : O) : (quiver x y X).Hom a b ⟶ obj a ⟶[SSet.{u}] obj b := by
  classical
  by_cases h : a = x ∧ b = y
  · rcases h with ⟨ha, hb⟩
    subst a
    subst b
    exact eqToHom (quiver_at x y X) ≫ f
  · exact eqToHom (quiver_other x y X a b h) ≫ initial.to _

/-- Read the supplied Hom map from the whole generator family. -/
def restrict (X : SSet.{u}) (obj : O → C)
    (f : ∀ a b : O, (quiver x y X).Hom a b ⟶ obj a ⟶[SSet.{u}] obj b) :
    X ⟶ obj x ⟶[SSet.{u}] obj y :=
  eqToHom (quiver_at x y X).symm ≫ f x y

/-- Reading the specified generator after extension returns its whole original Hom map. -/
@[simp]
theorem restrict_maps (X : SSet.{u}) (obj : O → C)
    (f : X ⟶ obj x ⟶[SSet.{u}] obj y) :
    restrict x y X obj (maps x y X obj f) = f := by
  classical
  simp [restrict, maps]

/-- The only remaining generating Homs are initial, so extension recovers the entire family. -/
@[simp]
theorem maps_restrict (X : SSet.{u}) (obj : O → C)
    (f : ∀ a b : O, (quiver x y X).Hom a b ⟶ obj a ⟶[SSet.{u}] obj b) :
    maps x y X obj (restrict x y X obj f) = f := by
  classical
  funext a b
  by_cases h : a = x ∧ b = y
  · rcases h with ⟨ha, hb⟩
    subst a
    subst b
    simp [maps, restrict]
  · apply (cancel_epi (eqToIso (quiver_other x y X a b h)).inv).1
    exact initial.hom_ext _ _

/-- The actual fixed-object generator family is equivalent to one original simplicial Hom map. -/
def mapEquiv (X : SSet.{u}) (obj : O → C) :
    (∀ a b : O, (quiver x y X).Hom a b ⟶ obj a ⟶[SSet.{u}] obj b) ≃
      (X ⟶ obj x ⟶[SSet.{u}] obj y) where
  toFun := restrict x y X obj
  invFun := maps x y X obj
  left_inv := maps_restrict x y X obj
  right_inv := restrict_maps x y X obj

/-- The genuine generator interpretation with the supplied original object function. -/
def interpretation (X : SSet.{u}) (obj : O → C)
    (f : X ⟶ obj x ⟶[SSet.{u}] obj y) : Interpretation (quiver x y X) C where
  obj := obj
  map := maps x y X obj f

/-- Its actual path extension sends the specified generator to the supplied whole Hom map. -/
theorem generator_extend (X : SSet.{u}) (obj : O → C)
    (f : X ⟶ obj x ⟶[SSet.{u}] obj y) :
    eqToHom (quiver_at x y X).symm ≫ generator (quiver x y X) x y ≫
      (interpretation x y X obj f).evalHom x y = f := by
  rw [Interpretation.generator_eval]
  exact restrict_maps x y X obj f

end CategoryTheory.SimplicialQuiver.SingleHom

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberEvaluation
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Universal ordinary diagram of a cofiber sequence of functors

A composable pair of natural transformations has one ordinary diagram over
its whole source category. If its objectwise pairs are cofiber sequences,
the same diagram lifts to the existing full category of cofiber sequences.
The source, middle, quotient, and all three morphism components remain the
original functors. No K-space comparison or homotopy is an input.
-/

public section

open CategoryTheory Limits

universe vB uB vC uC

namespace CategoryTheory.Waldhausen.SConstruction

section Diagram

variable {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C]
  (F₀ F₁ F₂ : B ⥤ C) (i : F₀ ⟶ F₁) (p : F₁ ⟶ F₂)

/-- The actual two-arrow natural-transformation diagram, evaluated on the
whole source category by the ordinary functor-category flip. -/
@[expose]
def functorSequenceDiagram : B ⥤ ComposableArrows C 2 :=
  (ComposableArrows.mk₂ i p).flip

/-- The first object is the original first functor value. -/
theorem functorSequenceDiagram_obj_zero (X : B) :
    ComposableArrows.obj' ((functorSequenceDiagram F₀ F₁ F₂ i p).obj X) 0 = F₀.obj X :=
  rfl

/-- The middle object is the original middle functor value. -/
theorem functorSequenceDiagram_obj_one (X : B) :
    ComposableArrows.obj' ((functorSequenceDiagram F₀ F₁ F₂ i p).obj X) 1 = F₁.obj X :=
  rfl

/-- The last object is the original last functor value. -/
theorem functorSequenceDiagram_obj_two (X : B) :
    ComposableArrows.obj' ((functorSequenceDiagram F₀ F₁ F₂ i p).obj X) 2 = F₂.obj X :=
  rfl

/-- The first structure map is the original natural-transformation component. -/
theorem functorSequenceDiagram_map_zero_one (X : B) :
    ComposableArrows.map' ((functorSequenceDiagram F₀ F₁ F₂ i p).obj X) 0 1 = i.app X :=
  rfl

/-- The second structure map is the original natural-transformation component. -/
theorem functorSequenceDiagram_map_one_two (X : B) :
    ComposableArrows.map' ((functorSequenceDiagram F₀ F₁ F₂ i p).obj X) 1 2 = p.app X :=
  rfl

end Diagram

section Cofiber

variable {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
  (F₀ F₁ F₂ : B ⥤ C) (i : F₀ ⟶ F₁) (p : F₁ ⟶ F₂)
  (h : ∀ X : B, IsCofiberSequence (i.app X) (p.app X))

/-- The same whole functor diagram in the existing category of cofiber
sequences, using only the source-given objectwise cofiber condition. -/
@[expose]
def cofiberFunctorSequenceLift : B ⥤ CofiberSequenceCategory C :=
  (cofiberSequenceProperty C).lift (functorSequenceDiagram F₀ F₁ F₂ i p)
    (fun X => by
      change IsCofiberSequence (i.app X) (p.app X)
      exact h X)

/-- Forgetting the cofiber condition returns the actual original diagram. -/
theorem cofiberFunctorSequenceLift_forget :
    cofiberFunctorSequenceLift F₀ F₁ F₂ i p h ⋙ CofiberSequenceCategory.forget C =
      functorSequenceDiagram F₀ F₁ F₂ i p :=
  rfl

/-- Source evaluation of the universal lift is the first functor. -/
theorem cofiberFunctorSequenceLift_source :
    cofiberFunctorSequenceLift F₀ F₁ F₂ i p h ⋙ CofiberSequenceCategory.source C = F₀ :=
  rfl

/-- Middle evaluation of the universal lift is the middle functor. -/
theorem cofiberFunctorSequenceLift_middle :
    cofiberFunctorSequenceLift F₀ F₁ F₂ i p h ⋙ CofiberSequenceCategory.middle C = F₁ :=
  rfl

/-- Quotient evaluation of the universal lift is the last functor. -/
theorem cofiberFunctorSequenceLift_quotient :
    cofiberFunctorSequenceLift F₀ F₁ F₂ i p h ⋙ CofiberSequenceCategory.quotient C = F₂ :=
  rfl

/-- Source maps retain the original first-functor component. -/
theorem cofiberFunctorSequenceLift_source_map {X Y : B} (f : X ⟶ Y) :
    (CofiberSequenceCategory.source C).map
      ((cofiberFunctorSequenceLift F₀ F₁ F₂ i p h).map f) = F₀.map f :=
  rfl

/-- Middle maps retain the original middle-functor component. -/
theorem cofiberFunctorSequenceLift_middle_map {X Y : B} (f : X ⟶ Y) :
    (CofiberSequenceCategory.middle C).map
      ((cofiberFunctorSequenceLift F₀ F₁ F₂ i p h).map f) = F₁.map f :=
  rfl

/-- Quotient maps retain the original last-functor component. -/
theorem cofiberFunctorSequenceLift_quotient_map {X Y : B} (f : X ⟶ Y) :
    (CofiberSequenceCategory.quotient C).map
      ((cofiberFunctorSequenceLift F₀ F₁ F₂ i p h).map f) = F₂.map f :=
  rfl

end Cofiber

end CategoryTheory.Waldhausen.SConstruction

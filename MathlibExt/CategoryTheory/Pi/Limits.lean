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

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Zero objects and pushouts in categories of families

Let I be an index type and C_i categories. Objects of the category ΠᵢC_i are families X_i and
morphisms are families of component maps. A family is a zero object exactly when each X_i is
zero. Chosen zero objects in all C_i therefore give the zero family i ↦ 0.

A square of families whose component squares are pushouts is a pushout in ΠᵢC_i. Its
descendant and the equations on its two legs are assembled componentwise, and uniqueness
follows componentwise. The indexing, object and morphism universes are independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

universe w u v

open CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory

variable {I : Type w} (C : I → Type u) [∀ i, Category.{v} (C i)]

namespace Pi

/-- Zero family from zero components.

For a family X in the category ΠᵢC_i, if X_i is a zero object in C_i for every i, then X is a
zero object. The unique maps to and from any other family are obtained from the unique
component maps. -/
theorem isZero_of_components {X : ∀ i, C i} (hX : ∀ i, IsZero (X i)) : IsZero X := by
  constructor
  · intro Y
    exact ⟨{ default := fun i => (hX i).to_ (Y i)
             uniq := fun f => funext fun i => (hX i).eq_of_src _ _ }⟩
  · intro Y
    exact ⟨{ default := fun i => (hX i).from_ (Y i)
             uniq := fun f => funext fun i => (hX i).eq_of_tgt _ _ }⟩

/-- Chosen zero object in a category of families.

If each category C_i has a zero object, the family i ↦ 0 is a zero object in ΠᵢC_i. This gives
a HasZeroObject instance with arbitrary indexing universe. -/
instance hasZeroObject [∀ i, HasZeroObject (C i)] : HasZeroObject (∀ i, C i) :=
  ⟨⟨fun i => (0 : C i), isZero_of_components C (fun i => isZero_zero (C i))⟩⟩

/-- Component characterization of a zero family.

For a family X in ΠᵢC_i, IsZero X holds if and only if every component X_i is zero. In the
forward direction, replacing just the i-th coordinate by any object tests the initial and
terminal properties of X_i. -/
theorem isZero_iff (X : ∀ i, C i) :
    IsZero X ↔ ∀ i, IsZero (X i) := by
  classical
  constructor
  · intro hX i
    constructor
    · intro Y
      let D : ∀ j, C j := Function.update X i Y
      refine ⟨{ default := by
                  simpa only [D, Function.update_self] using (hX.to_ D) i
                uniq := ?_ }⟩
      intro f
      let F : X ⟶ D := fun j => by
        by_cases hji : j = i
        · subst j
          simpa only [D, Function.update_self] using f
        · simpa only [D, Function.update_of_ne hji] using (𝟙 (X j))
      have hi := congrArg
        (fun g : X ⟶ D => g i ≫ eqToHom (Function.update_self i Y X))
        (hX.eq_of_src F (hX.to_ D))
      simpa [F, D, Category.assoc] using hi
    · intro Y
      let D : ∀ j, C j := Function.update X i Y
      refine ⟨{ default := by
                  simpa only [D, Function.update_self] using (hX.from_ D) i
                uniq := ?_ }⟩
      intro f
      let F : D ⟶ X := fun j => by
        by_cases hji : j = i
        · subst j
          simpa only [D, Function.update_self] using f
        · simpa only [D, Function.update_of_ne hji] using (𝟙 (X j))
      have hi := congrArg
        (fun g : D ⟶ X => eqToHom (Function.update_self i Y X).symm ≫ g i)
        (hX.eq_of_tgt F (hX.from_ D))
      simpa [F, D, Category.assoc] using hi
  · exact isZero_of_components C

/-- Pushout of families from component pushouts.

Let Z → X, Z → Y, X → P and Y → P be a square in ΠᵢC_i. If every coordinate square is a
pushout in C_i, then the family square is a pushout. Its universal map has the component
descendants supplied by those pushouts. -/
theorem isPushout_of_components {Z X Y P : ∀ i, C i}
    {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (hP : ∀ i, IsPushout (f i) (g i) (inl i) (inr i)) : IsPushout f g inl inr := by
  have hcomm : f ≫ inl = g ≫ inr := funext fun i => (hP i).w
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hcomm
    (fun s i => (hP i).desc (s.inl i) (s.inr i)
      (congrArg (fun q : Z ⟶ s.pt => q i) s.condition)) ?_ ?_ ?_)
  · intro s
    funext i
    exact (hP i).inl_desc _ _ _
  · intro s
    funext i
    exact (hP i).inr_desc _ _ _
  · intro s m hleft hright
    funext i
    apply (hP i).hom_ext
    · exact (congrArg (fun q : X ⟶ s.pt => q i) hleft).trans
        ((hP i).inl_desc _ _ _).symm
    · exact (congrArg (fun q : Y ⟶ s.pt => q i) hright).trans
        ((hP i).inr_desc _ _ _).symm

end Pi

end CategoryTheory

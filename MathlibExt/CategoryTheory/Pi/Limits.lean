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
# Zero objects and pushout squares in the native category of indexed families

Component zero objects give an explicit zero tuple, and every actual zero
family has zero components. Supplied component pushout universal properties
assemble with their original descendants, leg equations and uniqueness.

The zero-family characterization uses only the original categories, with
coordinate replacement and identity maps elsewhere. The index, object
and morphism universes are independent.
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

/-- A family of zero objects is a zero object in the actual Pi category. -/
theorem isZero_of_components {X : ∀ i, C i} (hX : ∀ i, IsZero (X i)) : IsZero X := by
  constructor
  · intro Y
    exact ⟨{ default := fun i => (hX i).to_ (Y i)
             uniq := fun f => funext fun i => (hX i).eq_of_src _ _ }⟩
  · intro Y
    exact ⟨{ default := fun i => (hX i).from_ (Y i)
             uniq := fun f => funext fun i => (hX i).eq_of_tgt _ _ }⟩

/-- Component zero objects supply a zero object without an index-size restriction. -/
instance hasZeroObject [∀ i, HasZeroObject (C i)] : HasZeroObject (∀ i, C i) :=
  ⟨⟨fun i => (0 : C i), isZero_of_components C (fun i => isZero_zero (C i))⟩⟩

/-- An actual family is zero precisely when each of its original components is zero. -/
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

/-- Actual component pushout universal properties assemble in all three independent universes. -/
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

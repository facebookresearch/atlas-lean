/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The category of short exact sequences

These declarations are extracted from `HomologySequenceFunctor` so that
short-exact-sequence infrastructure does not require complex homology.
The category, lifting functors and their characteristic equations retain
their original names and definitions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory.ShortComplex

variable {C : Type u} {D : Type u'}
  [Category.{v} C] [Category.{v'} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- The short-exact property as an `ObjectProperty` on `ShortComplex`. -/
abbrev isShortExact (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :
    ObjectProperty (ShortComplex C) :=
  ShortComplex.ShortExact

/-- The full subcategory of short exact short complexes. -/
abbrev ShortExactSequences (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  (isShortExact C).FullSubcategory

/-- Functoriality of short exact sequences under a functor preserving zero morphisms. -/
def mapFunctor (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact) :
    ShortExactSequences C ⥤ ShortExactSequences D :=
  (isShortExact D).lift ((isShortExact C).ι ⋙ F.mapShortComplex)
    (fun S => hF S.obj S.property)

@[simp]
lemma mapFunctor_obj_obj (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact)
    (S : ShortExactSequences C) :
    ((mapFunctor F hF).obj S).obj = S.obj.map F :=
  rfl

@[simp]
lemma mapFunctor_map_hom (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact)
    {S T : ShortExactSequences C} (f : S ⟶ T) :
    ((mapFunctor F hF).map f).hom = F.mapShortComplex.map f.hom :=
  rfl

/-- Lift a functorial family of short complexes that is pointwise short exact
to the category of short exact sequences. -/
def familyFunctor {X : Type*} [Category X] (F : X ⥤ ShortComplex C)
    (hF : ∀ x : X, (F.obj x).ShortExact) :
    X ⥤ ShortExactSequences C :=
  (isShortExact C).lift F hF

@[simp]
lemma familyFunctor_obj_obj {X : Type*} [Category X]
    (F : X ⥤ ShortComplex C) (hF : ∀ x : X, (F.obj x).ShortExact)
    (x : X) :
    ((familyFunctor F hF).obj x).obj = F.obj x :=
  rfl

@[simp]
lemma familyFunctor_map_hom {X : Type*} [Category X]
    (F : X ⥤ ShortComplex C) (hF : ∀ x : X, (F.obj x).ShortExact)
    {x y : X} (f : x ⟶ y) :
    ((familyFunctor F hF).map f).hom = F.map f :=
  rfl

section CanonicalSequences

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical cokernel sequence of a monomorphism is short exact. -/
theorem shortExact_cokernelSequence {X Y : A} (f : X ⟶ Y) [Mono f] :
    (cokernelSequence f).ShortExact := by
  have hmono : Mono (cokernelSequence f).f := by
    dsimp [cokernelSequence]
    infer_instance
  exact ShortExact.mk' (cokernelSequence_exact f) hmono inferInstance

/-- The canonical kernel sequence of an epimorphism is short exact. -/
theorem kernelSequence_shortExact {X Y : A} (f : X ⟶ Y) [Epi f] :
    (kernelSequence f).ShortExact := by
  have hepi : Epi (kernelSequence f).g := by
    dsimp [kernelSequence]
    infer_instance
  exact ShortExact.mk' (kernelSequence_exact f) inferInstance hepi

end CanonicalSequences

end CategoryTheory.ShortComplex

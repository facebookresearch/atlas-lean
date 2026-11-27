/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Presentable.BoundedPresheafMonomorphismFamily
public import MathlibExt.CategoryTheory.Presentable.PresheafMonomorphismFiltration

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace CategoryTheory.Presheaf.BoundedMonoFamilyTest

variable (E : Type u) [SmallCategory E]


/-- The original representative view is the canonical shared morphism predicate. -/
theorem sharedView (a : CategoryTheory.Arrow (Eᵒᵖ ⥤ Type u)) :
    boundedMonoArrows E a ↔ MorphismProperty.boundedPresheafMonomorphisms E a.hom := Iff.rfl

open scoped PresheafMonomorphismFiltration in
/-- The actual original cyclic intersection cell is an element of that SAME family view. -/
theorem actualFiltrationCell {A B : Eᵒᵖ ⥤ Type u} (f : A ⟶ B)
    (j : Subfunctor.PresheafSectionIndex B) (hj : ¬ IsMax j) :
    boundedMonoArrows E (Subfunctor.presheafMonoCell f j) :=
  Subfunctor.presheafMonoCell_bounded f j hj

example : ObjectProperty.EssentiallySmall.{u} (boundedMonoArrows E) :=
  boundedMonoArrows_essentiallySmall E

example : ∃ (K : Type u) (F : K → Arrow (Eᵒᵖ ⥤ Type u)),
    (∀ k, boundedMonoArrows E (F k)) ∧
      (∀ a, boundedMonoArrows E a → ∃ k, Nonempty (a ≅ F k)) := by
  obtain ⟨K, F, κ, hκ, hbot, _, hF, hcover, _, _, _, _, _⟩ := exists_bounded_mono_family E
  exact ⟨K, F, hF, hcover⟩

example : ∃ (K : Type u) (F : K → Arrow (Eᵒᵖ ⥤ Type u))
    (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
    letI : Fact κ.IsRegular := hκ
    letI : OrderBot κ.ord.ToType := hbot
    (∀ k, IsCardinalPresentable (F k).left κ ∧ IsCardinalPresentable (F k).right κ) ∧
      (MorphismProperty.ofHoms (fun k => (F k).hom)).IsSmall.{u} ∧
      (MorphismProperty.ofHoms (fun k => (F k).hom)).IsCardinalForSmallObjectArgument κ ∧
      (MorphismProperty.ofHoms (fun k => (F k).hom)).HasSmallObjectArgument.{u} := by
  obtain ⟨K, F, κ, hκ, hbot, _, _, _, hends, hsmall, heligible, hsoa, _⟩ :=
    exists_bounded_mono_family E
  exact ⟨K, F, κ, hκ, hbot, hends, hsmall, heligible, hsoa⟩

example : ∃ (K : Type u) (F : K → Arrow (Eᵒᵖ ⥤ Type u)),
    IsEmpty K ∧ ∀ k, (⊥ : ObjectProperty (Arrow (Eᵒᵖ ⥤ Type u))) (F k) := by
  obtain ⟨K, F, κ, hκ, hbot, _, hF, _, _, _, _, _, _⟩ :=
    exists_bounded_mono_family_of_property E (⊥ : ObjectProperty (Arrow (Eᵒᵖ ⥤ Type u)))
      bot_le
  exact ⟨K, F, ⟨fun k => hF k⟩, hF⟩

example : ∃ (K : Type u) (F : K → Arrow (Eᵒᵖ ⥤ Type u)),
    Nonempty (MorphismProperty.FunctorialFactorizationData
      (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp.llp
      (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp) := by
  obtain ⟨K, F, κ, hκ, hbot, _, _, _, _, _, _, _, hfac⟩ := exists_bounded_mono_family E
  exact ⟨K, F, hfac⟩

example : ∃ (K : Type u) (F : K → Arrow ((Discrete PEmpty)ᵒᵖ ⥤ Type u)),
    (∀ k, boundedMonoArrows (Discrete PEmpty) (F k)) ∧
      (∀ a, boundedMonoArrows (Discrete PEmpty) a → ∃ k, Nonempty (a ≅ F k)) := by
  obtain ⟨K, F, κ, hκ, hbot, _, hF, hcover, _, _, _, _, _⟩ :=
    exists_bounded_mono_family (Discrete PEmpty)
  exact ⟨K, F, hF, hcover⟩

end CategoryTheory.Presheaf.BoundedMonoFamilyTest

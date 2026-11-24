/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.Bicategory.Span.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# Quillen Q-construction for exact categories

For an exact category `C`, `QuillenQ C` has the same objects as `C` and
morphisms given by isomorphism classes of admissible spans
`X ←↞ M ↪ Y` where the left leg is an admissible epi and the right leg
is an admissible mono. Composition is via pullback, well-defined up to
span isomorphism.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Wrapper around objects of `C`; the `Category` instance on `QuillenQ C`
does not overlap the original `Category C`. -/
structure QuillenQ (C : Type u) where
  obj : C

namespace QuillenQ

variable {C : Type u}

@[inline]
def get (Q : QuillenQ C) : C :=
  Q.obj

def equiv : QuillenQ C ≃ C where
  toFun := get
  invFun := fun X => ⟨X⟩
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

@[simp]
theorem mk_get (Q : QuillenQ C) :
    (⟨get Q⟩ : QuillenQ C) = Q := by
  cases Q
  rfl

@[simp]
theorem get_mk (X : C) :
    get (⟨X⟩ : QuillenQ C) = X :=
  rfl

end QuillenQ

/-- Raw admissible span `X ←↞ M ↪ Y`. -/
abbrev QuillenSpan (X Y : C) :=
  Span (admissibleEpisOf C IsAdmissibleExact)
    (admissibleMonosOf C IsAdmissibleExact) X Y


private instance instSetoidQuillenSpan (X Y : C) :
    Setoid (QuillenSpan X Y) :=
  isIsomorphicSetoid (QuillenSpan X Y)

/-- Morphisms of `QuillenQ` are isomorphism classes of admissible spans. -/
abbrev QuillenQHom (X Y : QuillenQ C) :=
  Quotient (isIsomorphicSetoid (QuillenSpan X.obj Y.obj))


namespace QuillenQ

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Representative constructor for `QuillenQ` morphisms. -/
def mkHom {X Y : QuillenQ C} (S : QuillenSpan X.obj Y.obj) :
    QuillenQHom X Y :=
  Quotient.mk _ S


theorem mkHom_sound {X Y : QuillenQ C}
    {S₁ S₂ : QuillenSpan X.obj Y.obj} (e : S₁ ≅ S₂) :
    mkHom (X := X) (Y := Y) S₁ = mkHom S₂ :=
  Quotient.sound ⟨e⟩

theorem mkHom_eq_iff {X Y : QuillenQ C}
    {S₁ S₂ : QuillenSpan X.obj Y.obj} :
    mkHom (X := X) (Y := Y) S₁ = mkHom S₂ ↔ Nonempty (S₁ ≅ S₂) :=
  Quotient.eq

end QuillenQ

section CompIso

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {X Y Z : C}
  {S₁ : QuillenSpan X Y} {S₁' : QuillenSpan X Y}
  {S₂ : QuillenSpan Y Z} {S₂' : QuillenSpan Y Z}

/-- Isomorphism between composed spans from apex isomorphisms. -/
noncomputable def compSpanIso (e₁ : S₁ ≅ S₁') (e₂ : S₂ ≅ S₂') :
    Span.comp S₁ S₂ ≅ Span.comp S₁' S₂' :=
  (CategoryTheory.Bicategory.whiskerRightIso
      (B := Span.SpanBicat C (admissibleEpisOf C IsAdmissibleExact)
        (admissibleMonosOf C IsAdmissibleExact)) e₁ S₂).trans
    (CategoryTheory.Bicategory.whiskerLeftIso
      (B := Span.SpanBicat C (admissibleEpisOf C IsAdmissibleExact)
        (admissibleMonosOf C IsAdmissibleExact)) S₁' e₂)

theorem comp_respects_iso {X Y Z : C}
    {S₁ S₁' : QuillenSpan X Y} {S₂ S₂' : QuillenSpan Y Z}
    (h₁ : Nonempty (S₁ ≅ S₁')) (h₂ : Nonempty (S₂ ≅ S₂')) :
    Nonempty (Span.comp S₁ S₂ ≅ Span.comp S₁' S₂') := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨compSpanIso e₁ e₂⟩

end CompIso

section CategoryInstance

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Noncomputable composition on `QuillenQ` via `Quotient.map₂ Span.comp`. -/
noncomputable def quillenComp {X Y Z : QuillenQ C}
    (f : QuillenQHom X Y) (g : QuillenQHom Y Z) :
    QuillenQHom X Z :=
  Quotient.map₂
    (fun (S₁ : QuillenSpan X.obj Y.obj)
        (S₂ : QuillenSpan Y.obj Z.obj) =>
      Span.comp S₁ S₂)
    (fun _ _ h₁ _ _ h₂ => comp_respects_iso h₁ h₂) f g

noncomputable def quillenId (X : QuillenQ C) :
    QuillenQHom X X :=
  Quotient.mk (isIsomorphicSetoid (QuillenSpan X.obj X.obj))
    (Span.id (c := X.obj) : QuillenSpan X.obj X.obj)

private theorem quillenId_comp_aux {X Y : QuillenQ C}
    (S : QuillenSpan X.obj Y.obj) :
    Nonempty (Span.comp
        (Span.id (c := X.obj) : QuillenSpan X.obj X.obj) S ≅ S) :=
  ⟨Span.SpanBicat.leftUnitor (c := ⟨X.obj⟩) (c' := ⟨Y.obj⟩) S⟩

private theorem quillenComp_id_aux {X Y : QuillenQ C}
    (S : QuillenSpan X.obj Y.obj) :
    Nonempty (Span.comp S
        (Span.id (c := Y.obj) : QuillenSpan Y.obj Y.obj) ≅ S) :=
  ⟨Span.SpanBicat.rightUnitor (c := ⟨X.obj⟩) (c' := ⟨Y.obj⟩) S⟩

private theorem quillenAssoc_aux {W X Y Z : QuillenQ C}
    (S₁ : QuillenSpan W.obj X.obj) (S₂ : QuillenSpan X.obj Y.obj)
    (S₃ : QuillenSpan Y.obj Z.obj) :
    Nonempty (Span.comp (Span.comp S₁ S₂) S₃ ≅
      Span.comp S₁ (Span.comp S₂ S₃)) := by
  exact ⟨Span.SpanBicat.associator (c₁ := ⟨W.obj⟩) (c₂ := ⟨X.obj⟩)
    (c₃ := ⟨Y.obj⟩) (c₄ := ⟨Z.obj⟩) S₁ S₂ S₃⟩

noncomputable instance instCategoryQuillenQ :
    Category (QuillenQ C) where
  Hom X Y := QuillenQHom X Y
  id X := quillenId X
  comp {X Y Z} f g := quillenComp f g
  id_comp := by
    intro X Y f
    refine Quotient.inductionOn f ?_
    intro S
    change quillenComp (quillenId X) (Quotient.mk _ S) =
        Quotient.mk _ S
    have h : Span.comp
          (Span.id (c := X.obj) : QuillenSpan X.obj X.obj) S ≈ S :=
        quillenId_comp_aux S
    exact Quotient.sound h
  comp_id := by
    intro X Y f
    refine Quotient.inductionOn f ?_
    intro S
    change quillenComp (Quotient.mk _ S) (quillenId Y) =
        Quotient.mk _ S
    have h : Span.comp S
          (Span.id (c := Y.obj) : QuillenSpan Y.obj Y.obj) ≈ S :=
        quillenComp_id_aux S
    exact Quotient.sound h
  assoc := by
    intro W X Y Z f g h
    refine Quotient.inductionOn f ?_
    intro S₁
    refine Quotient.inductionOn g ?_
    intro S₂
    refine Quotient.inductionOn h ?_
    intro S₃
    change
        quillenComp (quillenComp (Quotient.mk _ S₁)
          (Quotient.mk _ S₂)) (Quotient.mk _ S₃) =
        quillenComp (Quotient.mk _ S₁)
          (quillenComp (Quotient.mk _ S₂) (Quotient.mk _ S₃))
    have heq :
        Span.comp (Span.comp S₁ S₂) S₃ ≈
          Span.comp S₁ (Span.comp S₂ S₃) :=
        quillenAssoc_aux S₁ S₂ S₃
    exact Quotient.sound heq

@[simp]
theorem mkHom_id (X : QuillenQ C) :
    (QuillenQ.mkHom (X := X) (Y := X)
        (Span.id (c := X.obj) : QuillenSpan X.obj X.obj) : X ⟶ X) =
      (𝟙 X : X ⟶ X) :=
  rfl

@[simp]
theorem mkHom_comp {X Y Z : QuillenQ C}
    (S₁ : QuillenSpan X.obj Y.obj) (S₂ : QuillenSpan Y.obj Z.obj) :
    quillenComp (QuillenQ.mkHom (X := X) (Y := Y) S₁)
        (QuillenQ.mkHom (X := Y) (Y := Z) S₂) =
      QuillenQ.mkHom (X := X) (Y := Z) (Span.comp S₁ S₂) :=
  rfl

end CategoryInstance

end AlgebraicKTheory

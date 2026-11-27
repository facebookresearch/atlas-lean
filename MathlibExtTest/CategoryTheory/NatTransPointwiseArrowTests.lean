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

import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Images

/-! # Tests for pointwise arrow functors -/

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace MathlibExtTest.CategoryTheory.NatTransPointwiseArrowTests

variable {B : Type u₁} [Category.{v₁} B]
variable {I : Type u₂} [Category.{v₂} I]
variable {C : Type u₃} [Category.{v₃} C]

variable {P Q : B ⥤ C} (η : P ⟶ Q)

example : B ⥤ Arrow C :=
  NatTrans.arrow η

example (b : B) : (NatTrans.arrow η).obj b = Arrow.mk (η.app b) := by
  simp

example {b b' : B} (f : b ⟶ b') :
    ((NatTrans.arrow η).map f).left = P.map f := by
  simp

variable {F G : B ⥤ I ⥤ C} (α : F ⟶ G)

example : B ⥤ I ⥤ Arrow C :=
  NatTrans.pointwiseArrow α

example (b : B) (i : I) :
    ((NatTrans.pointwiseArrow α).obj b).obj i = Arrow.mk ((α.app b).app i) := by
  simp

example (b : B) {i i' : I} (f : i ⟶ i') :
    ((NatTrans.pointwiseArrow α).obj b).map f =
      Arrow.homMk ((F.obj b).map f) ((G.obj b).map f) ((α.app b).naturality f) :=
  NatTrans.pointwiseArrow_obj_map α b f

example {b b' : B} (f : b ⟶ b') (i : I) :
    ((NatTrans.pointwiseArrow α).map f).app i =
      Arrow.homMk ((F.map f).app i) ((G.map f).app i)
        (congr_app (α.naturality f) i) :=
  NatTrans.pointwiseArrow_map_app α f i

example {b b' : B} (f : b ⟶ b') (i : I) :
    (((NatTrans.pointwiseArrow α).map f).app i).left = (F.map f).app i := by
  simp

example {b b' : B} (f : b ⟶ b') (i : I) :
    (((NatTrans.pointwiseArrow α).map f).app i).right = (G.map f).app i := by
  simp

example (b : B) :
    (NatTrans.pointwiseArrow α).map (𝟙 b) =
      𝟙 ((NatTrans.pointwiseArrow α).obj b) :=
  (NatTrans.pointwiseArrow α).map_id b

example {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    (NatTrans.pointwiseArrow α).map (f ≫ g) =
      (NatTrans.pointwiseArrow α).map f ≫ (NatTrans.pointwiseArrow α).map g :=
  (NatTrans.pointwiseArrow α).map_comp f g

example (H : B ⥤ I ⥤ C) (b : B) (i : I) :
    (((NatTrans.pointwiseArrow (𝟙 H)).obj b).obj i).hom =
      𝟙 ((H.obj b).obj i) := by
  simp

section TerminalIndex

variable {F' G' : B ⥤ Discrete PUnit ⥤ C} (β : F' ⟶ G')

example (b : B) :
    ((NatTrans.pointwiseArrow β).obj b).obj (Discrete.mk PUnit.unit) =
      Arrow.mk ((β.app b).app (Discrete.mk PUnit.unit)) := by
  simp

end TerminalIndex

section ImageConsumer

variable [Limits.HasImages C] [Limits.HasImageMaps C]

noncomputable example : B ⥤ I ⥤ C :=
  NatTrans.pointwiseArrow α ⋙
    (Functor.whiskeringRight I (Arrow C) C).obj (Limits.im (C := C))

end ImageConsumer

section ArrowFunctorIsomorphisms

variable {L R L' R' : B ⥤ C} (η₀ : L ⟶ R) (θ₀ : L' ⟶ R')
  (a : ∀ X : B, L.obj X ≅ L'.obj X) (b : ∀ X : B, R.obj X ≅ R'.obj X)
  (ha : ∀ {X Y : B} (f : X ⟶ Y), L.map f ≫ (a Y).hom = (a X).hom ≫ L'.map f)
  (hb : ∀ {X Y : B} (f : X ⟶ Y), R.map f ≫ (b Y).hom = (b X).hom ≫ R'.map f)
  (hs : ∀ X : B, (a X).hom ≫ θ₀.app X = η₀.app X ≫ (b X).hom)

example (X : B) :
    ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).hom.app X).left ≫
      ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).inv.app X).left = 𝟙 (L.obj X) := by
  simp

example (X : B) :
    ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).inv.app X).left ≫
      ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).hom.app X).left = 𝟙 (L'.obj X) := by
  simp

example (X : B) :
    ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).hom.app X).right ≫
      ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).inv.app X).right = 𝟙 (R.obj X) := by
  simp

example (X : B) :
    ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).inv.app X).right ≫
      ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).hom.app X).right = 𝟙 (R'.obj X) := by
  simp

example {X Y : B} (f : X ⟶ Y) :
    ((NatTrans.arrow η₀).map f).left ≫
        ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).hom.app Y).left =
      ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).hom.app X).left ≫
        ((NatTrans.arrow θ₀).map f).left := by
  simpa using ha f

example {X Y : B} (f : X ⟶ Y) :
    ((NatTrans.arrow η₀).map f).right ≫
        ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).hom.app Y).right =
      ((NatTrans.arrowFunctorIso η₀ θ₀ a b ha hb hs).hom.app X).right ≫
        ((NatTrans.arrow θ₀).map f).right := by
  simpa using hb f

variable (c : L ≅ L') (d : R ≅ R')
  (h : ∀ X : B, c.hom.app X ≫ θ₀.app X = η₀.app X ≫ d.hom.app X)

example (X : B) :
    ((NatTrans.arrowFunctorNatIso η₀ θ₀ c d h).hom.app X).left ≫
      ((NatTrans.arrowFunctorNatIso η₀ θ₀ c d h).inv.app X).left = 𝟙 (L.obj X) := by
  simp

example (X : B) :
    ((NatTrans.arrowFunctorNatIso η₀ θ₀ c d h).inv.app X).left ≫
      ((NatTrans.arrowFunctorNatIso η₀ θ₀ c d h).hom.app X).left = 𝟙 (L'.obj X) := by
  simp

example (X : B) :
    ((NatTrans.arrowFunctorNatIso η₀ θ₀ c d h).hom.app X).right ≫
      ((NatTrans.arrowFunctorNatIso η₀ θ₀ c d h).inv.app X).right = 𝟙 (R.obj X) := by
  simp

example (X : B) :
    ((NatTrans.arrowFunctorNatIso η₀ θ₀ c d h).inv.app X).right ≫
      ((NatTrans.arrowFunctorNatIso η₀ θ₀ c d h).hom.app X).right = 𝟙 (R'.obj X) := by
  simp

end ArrowFunctorIsomorphisms

#print axioms CategoryTheory.NatTrans.arrow
#print axioms CategoryTheory.NatTrans.pointwiseArrow
#print axioms CategoryTheory.NatTrans.arrowFunctorIso_hom_left
#print axioms CategoryTheory.NatTrans.arrowFunctorIso_hom_right
#print axioms CategoryTheory.NatTrans.arrowFunctorIso_inv_left
#print axioms CategoryTheory.NatTrans.arrowFunctorIso_inv_right
#print axioms CategoryTheory.NatTrans.arrowFunctorNatIso_hom_left
#print axioms CategoryTheory.NatTrans.arrowFunctorNatIso_hom_right
#print axioms CategoryTheory.NatTrans.arrowFunctorNatIso_inv_left
#print axioms CategoryTheory.NatTrans.arrowFunctorNatIso_inv_right

end MathlibExtTest.CategoryTheory.NatTransPointwiseArrowTests

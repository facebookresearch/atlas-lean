/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Original weak-category restriction of a Waldhausen exact functor

The exact functor's actual object map and actual weak morphism map restrict
to the original weak wide categories. Equality, identity and composition
retain those original maps; no alternate weak-equivalence relation is used.
-/

@[expose] public section
set_option autoImplicit false

universe uC vC uD vD uE vE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Waldhausen

variable (C : Type uC) [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original category `wC`, with all original objects and only original weak maps. -/
abbrev WeakCategory := WideSubcategory (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C))

/-- The original weak-category inclusion retains the original objects and maps. -/
abbrev weakCategoryInclusion : WeakCategory C ⥤ C :=
  wideSubcategoryInclusion (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C))

end CategoryTheory.Waldhausen


namespace CategoryTheory.Functor.IsWaldhausenExact

open CategoryTheory.Waldhausen

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {E : Type uE} [Category.{vE} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]
variable {F G : C ⥤ D}

/-- The actual exact functor restricts to the original weak wide categories. -/
def mapWeakCategory (hF : F.IsWaldhausenExact) :
    WideSubcategory (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)) ⥤
      WideSubcategory (WaldhausenCategoryWithoutGluing.weakEquivalences (C := D)) where
  obj X := ⟨F.obj X.obj⟩
  map f := ⟨F.map f.hom, hF.map_weakEquivalence f.hom f.property⟩
  map_id X := by apply WideSubcategory.hom_ext; exact F.map_id X.obj
  map_comp f g := by apply WideSubcategory.hom_ext; exact F.map_comp f.hom g.hom

/-- The original object and morphism maps determine the same weak restriction. -/
theorem mapWeakCategory_eq (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (h : F = G) :
    hF.mapWeakCategory = hG.mapWeakCategory := by
  subst G
  rfl

/-- Original identity gives the actual weak-category identity. -/
theorem mapWeakCategory_id :
    (Functor.IsWaldhausenExact.id (C := C)).mapWeakCategory =
      𝟭 (WideSubcategory (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C))) := rfl

/-- Original source-first exact-functor composition gives weak restriction composition. -/
theorem mapWeakCategory_comp {K : D ⥤ E} (hF : F.IsWaldhausenExact)
    (hK : K.IsWaldhausenExact) :
    (hF.comp hK).mapWeakCategory = hF.mapWeakCategory ⋙ hK.mapWeakCategory := rfl

/-- The actual weak functor retains the entire original object value. -/
theorem mapWeakCategory_obj (hF : F.IsWaldhausenExact) (X : WeakCategory C) :
    (hF.mapWeakCategory.obj X).obj = F.obj X.obj := rfl

/-- The actual weak functor retains the entire original morphism value. -/
theorem mapWeakCategory_map_hom (hF : F.IsWaldhausenExact)
    {X Y : WeakCategory C} (f : X ⟶ Y) :
    (hF.mapWeakCategory.map f).hom = F.map f.hom := rfl

/-- Forgetting the original weak functor is literally the original functor after inclusion. -/
theorem mapWeakCategory_inclusion (hF : F.IsWaldhausenExact) :
    hF.mapWeakCategory ⋙ weakCategoryInclusion D = weakCategoryInclusion C ⋙ F := rfl


end CategoryTheory.Functor.IsWaldhausenExact

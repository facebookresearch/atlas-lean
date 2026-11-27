/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.CoproductExactFunctorIso

/-!
# Clients for the actual exact-functor coproduct comparison

The four original category universes remain independent. Both actual
cocone injections and the whole original functor naturality are retained.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen

universe uA vA uB vB

namespace MathlibExtTest.KTheory.Waldhausen.CoproductExactFunctorIsoTests

variable {A : Type uA} [Category.{vA} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
variable {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
variable {F : A ⥤ B} (hF : F.IsWaldhausenExact)

/-- The whole original source and target coproduct functors have the actual comparison Iso. -/
def originalCoproductIso :
    waldhausenCoproductFunctor A ⋙ F ≅ F.prod F ⋙ waldhausenCoproductFunctor B :=
  hF.waldhausenCoproductIso

/-- Every actual original pair map retains the entire comparison naturality square. -/
theorem originalNaturality {p q : A × A} (φ : p ⟶ q) :
    (waldhausenCoproductFunctor A ⋙ F).map φ ≫ (hF.waldhausenCoproductIso).hom.app q =
      (hF.waldhausenCoproductIso).hom.app p ≫
        (F.prod F ⋙ waldhausenCoproductFunctor B).map φ :=
  (hF.waldhausenCoproductIso).hom.naturality φ

/-- The original first cocone injection is retained at both original category levels. -/
theorem originalFirstInjection (X Y : A) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
    let d : BinaryCofan (F.obj X) (F.obj Y) :=
      (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).cocone
    F.map c.inl ≫ (hF.coproductCoconeIso X Y).hom = d.inl :=
  hF.coproductCoconeIso_hom_inl X Y

/-- The same original comparison retains the second cocone injection. -/
theorem originalSecondInjection (X Y : A) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
    let d : BinaryCofan (F.obj X) (F.obj Y) :=
      (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).cocone
    F.map c.inr ≫ (hF.coproductCoconeIso X Y).hom = d.inr :=
  hF.coproductCoconeIso_hom_inr X Y

/-- The full actual comparison keeps both whole object transports and the same stock arrow. -/
theorem originalWholeComponent (p : A × A) :
    (hF.waldhausenCoproductIso).hom.app p =
      F.map (eqToHom (waldhausenCoproductFunctor_obj A p)) ≫
        (hF.coproductCoconeIso p.1 p.2).hom ≫
          eqToHom (waldhausenCoproductFunctor_obj B (F.obj p.1, F.obj p.2)).symm := by
  rw [hF.waldhausenCoproductIso_hom_app]
  exact hF.coproductIsoComponent_hom p

end MathlibExtTest.KTheory.Waldhausen.CoproductExactFunctorIsoTests

end

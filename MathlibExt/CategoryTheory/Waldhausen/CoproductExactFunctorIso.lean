/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductFunctor
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual coproduct preservation by Waldhausen exact functors

The original exact functor preserves the original chosen zero-source
pushout. Its image of the source zero is zero, so the image cocone is
an actual binary coproduct. The stock comparison of colimit cocones
retains both original injections and supplies a full natural isomorphism
between the same original coproduct functors.

All source and target object and morphism universes are independent.
No gluing or preservation outcome is an input.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uA vA uB vB

namespace CategoryTheory.Functor.IsWaldhausenExact

open CategoryTheory.Waldhausen

variable {A : Type uA} [Category.{vA} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
variable {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
variable {F : A ⥤ B} (hF : F.IsWaldhausenExact)

/-- The actual image of the original chosen coproduct cocone is colimiting,
from its mapped zero-source pushout and the actual zero image `F(0)`. -/
def mappedCoproductCoconeIsColimit (X Y : A) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
    IsColimit (BinaryCofan.mk (F.map c.inl) (F.map c.inr)) := by
  let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
  let z := isZero_zero A
  let i : (0 : A) ⟶ X := z.to_ X
  let f : (0 : A) ⟶ Y := z.to_ Y
  have hP : IsPushout f i c.inr c.inl := by
    have h := IsPushout.of_isColimit_binaryCofan_of_isInitial
      (binaryCoproductColimitCocone A (pair X Y)).isColimit z.isInitial
    have hX : z.isInitial.to X = i := z.eq_of_src _ _
    have hY : z.isInitial.to Y = f := z.eq_of_src _ _
    rw [hX, hY] at h
    exact h
  have hi : IsCofibration i := WaldhausenCategoryWithoutGluing.zero_isCofibration X i
  have hImage : IsPushout (F.map f) (F.map i) (F.map c.inr) (F.map c.inl) :=
    hF.map_pushout i f c.inr c.inl hi hP
  exact isBinaryCoproductOfIsInitialIsPushout (pair (F.obj X) (F.obj Y))
    (BinaryCofan.mk (F.map c.inl) (F.map c.inr))
    (hF.map_isZero z).isInitial (F.map i) (F.map f) hImage.flip.isColimit

/-- The stock original colimit comparison from the image coproduct cocone
to the target's original chosen coproduct cocone. -/
def coproductCoconeIso (X Y : A) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
    let d : BinaryCofan (F.obj X) (F.obj Y) :=
      (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).cocone
    F.obj c.pt ≅ d.pt :=
  IsColimit.coconePointUniqueUpToIso (mappedCoproductCoconeIsColimit hF X Y)
    (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).isColimit

/-- The entire first injection is retained by the actual stock comparison. -/
theorem coproductCoconeIso_hom_inl (X Y : A) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
    let d : BinaryCofan (F.obj X) (F.obj Y) :=
      (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).cocone
    F.map c.inl ≫ (coproductCoconeIso hF X Y).hom = d.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (mappedCoproductCoconeIsColimit hF X Y)
    (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).isColimit
    ⟨WalkingPair.left⟩

/-- The entire second injection is retained by the same stock comparison. -/
theorem coproductCoconeIso_hom_inr (X Y : A) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
    let d : BinaryCofan (F.obj X) (F.obj Y) :=
      (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).cocone
    F.map c.inr ≫ (coproductCoconeIso hF X Y).hom = d.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (mappedCoproductCoconeIsColimit hF X Y)
    (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).isColimit
    ⟨WalkingPair.right⟩

/-- Both actual image maps give the whole naturality square of the original
chosen coproduct cocones. -/
theorem coproductCoconeIso_naturality {X Y X' Y' : A} (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (binaryCoproductMap A f g) ≫ (coproductCoconeIso hF X' Y').hom =
      (coproductCoconeIso hF X Y).hom ≫ binaryCoproductMap B (F.map f) (F.map g) := by
  apply BinaryCofan.IsColimit.hom_ext (mappedCoproductCoconeIsColimit hF X Y)
  · rw [BinaryCofan.mk_inl, ← Category.assoc, ← F.map_comp, binaryCoproductMap_inl,
      F.map_comp, Category.assoc, coproductCoconeIso_hom_inl]
    rw [← Category.assoc, coproductCoconeIso_hom_inl, binaryCoproductMap_inl]
  · rw [BinaryCofan.mk_inr, ← Category.assoc, ← F.map_comp, binaryCoproductMap_inr,
      F.map_comp, Category.assoc, coproductCoconeIso_hom_inr]
    rw [← Category.assoc, coproductCoconeIso_hom_inr, binaryCoproductMap_inr]

/-- The actual comparison between the original whole functor objects,
using only their exported original cocone-object readouts. -/
def coproductIsoComponent (p : A × A) :
    (waldhausenCoproductFunctor A ⋙ F).obj p ≅
      (F.prod F ⋙ waldhausenCoproductFunctor B).obj p :=
  F.mapIso (eqToIso (waldhausenCoproductFunctor_obj A p)) ≪≫
    coproductCoconeIso hF p.1 p.2 ≪≫
      (eqToIso (waldhausenCoproductFunctor_obj B (F.obj p.1, F.obj p.2))).symm

/-- The whole original comparison arrow retains both original object
transports and the stock image-cocone comparison. -/
theorem coproductIsoComponent_hom (p : A × A) :
    (coproductIsoComponent hF p).hom =
      F.map (eqToHom (waldhausenCoproductFunctor_obj A p)) ≫
        (coproductCoconeIso hF p.1 p.2).hom ≫
          eqToHom (waldhausenCoproductFunctor_obj B (F.obj p.1, F.obj p.2)).symm := rfl

/-- Every original pair morphism gives the complete actual functor naturality square. -/
theorem coproductIsoComponent_naturality {p q : A × A} (φ : p ⟶ q) :
    (waldhausenCoproductFunctor A ⋙ F).map φ ≫ (coproductIsoComponent hF q).hom =
      (coproductIsoComponent hF p).hom ≫ (F.prod F ⋙ waldhausenCoproductFunctor B).map φ := by
  dsimp only [Functor.comp_map, Functor.prod_obj, Functor.prod_map]
  rw [coproductIsoComponent_hom, coproductIsoComponent_hom,
    waldhausenCoproductFunctor_map, waldhausenCoproductFunctor_map]
  have h := congrArg
    (fun k => F.map (eqToHom (waldhausenCoproductFunctor_obj A p)) ≫ k ≫
      eqToHom (waldhausenCoproductFunctor_obj B (F.obj q.1, F.obj q.2)).symm)
    (coproductCoconeIso_naturality hF φ.1 φ.2)
  simpa only [Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- The original exact functor preserves the actual original chosen binary
coproduct functor, with the entire stock comparison and naturality retained. -/
def waldhausenCoproductIso :
    waldhausenCoproductFunctor A ⋙ F ≅ F.prod F ⋙ waldhausenCoproductFunctor B :=
  NatIso.ofComponents (coproductIsoComponent hF) (coproductIsoComponent_naturality hF)

/-- Every whole component is the actual original cocone comparison. -/
theorem waldhausenCoproductIso_hom_app (p : A × A) :
    (waldhausenCoproductIso hF).hom.app p = (coproductIsoComponent hF p).hom := rfl

end CategoryTheory.Functor.IsWaldhausenExact

end

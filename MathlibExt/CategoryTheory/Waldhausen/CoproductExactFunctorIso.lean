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
# Coproduct comparisons for Waldhausen exact functors

Let F:A → B be a Waldhausen exact functor between categories with zero
objects and Waldhausen cofibration, weak-equivalence and pushout axioms.
The image of the chosen coproduct cocone for X,Y is colimiting for
F(X),F(Y), because F preserves its zero-source pushout.

The resulting comparison F(X⊔Y) ≅ F(X)⊔F(Y) preserves both coproduct
injections and is natural in maps of the two summands. Its components
form a natural isomorphism between F composed with the chosen coproduct
functor and the target coproduct functor composed with F×F.
Source and target object and morphism universes are independent.
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

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

For X,Y in A, the binary cocone with apex F(X⊔Y) and legs F(ι_X),F(ι_Y) is a coproduct cocone of
F(X),F(Y). -/
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

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

The canonical isomorphism η_{X,Y}:F(X⊔Y) ≅ F(X)⊔F(Y) between the image coproduct cocone and the
chosen target coproduct. -/
def coproductCoconeIso (X Y : A) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
    let d : BinaryCofan (F.obj X) (F.obj Y) :=
      (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).cocone
    F.obj c.pt ≅ d.pt :=
  IsColimit.coconePointUniqueUpToIso (mappedCoproductCoconeIsColimit hF X Y)
    (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).isColimit

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

The forward comparison η_{X,Y} satisfies η_{X,Y}∘F(ι_X)=ι_{F(X)}. -/
theorem coproductCoconeIso_hom_inl (X Y : A) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
    let d : BinaryCofan (F.obj X) (F.obj Y) :=
      (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).cocone
    F.map c.inl ≫ (coproductCoconeIso hF X Y).hom = d.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (mappedCoproductCoconeIsColimit hF X Y)
    (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).isColimit
    ⟨WalkingPair.left⟩

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

The forward comparison η_{X,Y} satisfies η_{X,Y}∘F(ι_Y)=ι_{F(Y)}. -/
theorem coproductCoconeIso_hom_inr (X Y : A) :
    let c : BinaryCofan X Y := (binaryCoproductColimitCocone A (pair X Y)).cocone
    let d : BinaryCofan (F.obj X) (F.obj Y) :=
      (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).cocone
    F.map c.inr ≫ (coproductCoconeIso hF X Y).hom = d.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (mappedCoproductCoconeIsColimit hF X Y)
    (binaryCoproductColimitCocone B (pair (F.obj X) (F.obj Y))).isColimit
    ⟨WalkingPair.right⟩

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

For f:X → X′ and g:Y → Y′, the comparisons satisfy η_{X′,Y′}∘F(f⊔g)=(F(f)⊔F(g))∘η_{X,Y}. -/
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

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

At a pair (X,Y), the component isomorphism from the value of F∘⊔_A to the value of ⊔_B∘(F×F),
obtained from η_{X,Y} through the chosen apex identifications. -/
def coproductIsoComponent (p : A × A) :
    (waldhausenCoproductFunctor A ⋙ F).obj p ≅
      (F.prod F ⋙ waldhausenCoproductFunctor B).obj p :=
  F.mapIso (eqToIso (waldhausenCoproductFunctor_obj A p)) ≪≫
    coproductCoconeIso hF p.1 p.2 ≪≫
      (eqToIso (waldhausenCoproductFunctor_obj B (F.obj p.1, F.obj p.2))).symm

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

Under the chosen source and target coproduct apex identifications, the forward component of F∘⊔_A ≅
⊔_B∘(F×F) is the cocone comparison η_{X,Y}. -/
theorem coproductIsoComponent_hom (p : A × A) :
    (coproductIsoComponent hF p).hom =
      F.map (eqToHom (waldhausenCoproductFunctor_obj A p)) ≫
        (coproductCoconeIso hF p.1 p.2).hom ≫
          eqToHom (waldhausenCoproductFunctor_obj B (F.obj p.1, F.obj p.2)).symm := rfl

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

For a pair morphism (f,g), the component comparisons of F∘⊔_A and ⊔_B∘(F×F) form the naturality
square of these two functors. -/
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

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

The natural isomorphism F∘⊔_A ≅ ⊔_B∘(F×F), with components given by the canonical coproduct cocone
comparisons. -/
def waldhausenCoproductIso :
    waldhausenCoproductFunctor A ⋙ F ≅ F.prod F ⋙ waldhausenCoproductFunctor B :=
  NatIso.ofComponents (coproductIsoComponent hF) (coproductIsoComponent_naturality hF)

/-- Let A,B have zero objects and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. Let F:A → B be Waldhausen exact,
preserving zero objects, cofibrations, weak equivalences and pushouts
along cofibrations. Use the chosen zero-source coproducts in A and B.

The forward natural transformation of F∘⊔_A ≅ ⊔_B∘(F×F) has at each pair (X,Y) the canonical
component coproduct isomorphism. -/
theorem waldhausenCoproductIso_hom_app (p : A × A) :
    (waldhausenCoproductIso hF).hom.app p = (coproductIsoComponent hF p).hom := rfl

end CategoryTheory.Functor.IsWaldhausenExact

end

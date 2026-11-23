/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslation
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationAction

/-!
# Translation equivariance of the additive S⁻¹S projection

Left addition by a fixed object defines an endofunctor of the one-coordinate
translation category.  Its arrow formula uses the same stabilizer swap as
first-coordinate translation on additive `S⁻¹S`.  The canonical
stabilized arrow from `X` to `A ⊞ X` is natural, and first-coordinate
translation on pairs lies strictly over this base endofunctor.

This is the categorical first layer of spectral-sequence equivariance.  It
constructs no right-comma diagram map, chain map, filtration map,
localization comparison, or spectral-sequence collapse.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS
namespace Translation

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Add a fixed object on the left in the one-coordinate translation
category. -/
abbrev translateObj (A : C) (X : Translation C) : Translation C :=
  ⟨A ⊞ X.of⟩

namespace RawHom

/-- Translate a raw one-coordinate arrow by a fixed left summand. -/
noncomputable def translate (A : C) {X Y : Translation C}
    (f : RawHom X Y) :
    RawHom (translateObj A X) (translateObj A Y) where
  stabilizer := f.stabilizer
  hom := (swapStabilizerIso A f.stabilizer X.of).trans
    (biprod.mapIso (Iso.refl A) f.hom)

omit [HasZeroObject C] in
/-- Translation respects change of stabilizer. -/
theorem translate_rel (A : C) {X Y : Translation C}
    {f g : RawHom X Y} (h : f.Rel g) :
    (f.translate A).Rel (g.translate A) := by
  obtain ⟨e, h⟩ := h
  refine ⟨e, ?_⟩
  change (stabilizerIso e (A ⊞ X.of)).trans
      ((swapStabilizerIso A g.stabilizer X.of).trans
        (biprod.mapIso (Iso.refl A) g.hom)) =
    (swapStabilizerIso A f.stabilizer X.of).trans
      (biprod.mapIso (Iso.refl A) f.hom)
  rw [← h, ← Iso.trans_assoc,
    stabilizerIso_trans_swapStabilizerIso, Iso.trans_assoc]
  apply Iso.ext
  ext <;> simp [stabilizerIso, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Translation preserves the raw identity modulo change of stabilizer. -/
theorem translate_id_rel (A : C) (X : Translation C) :
    (RawHom.id X).translate A |>.Rel
      (RawHom.id (translateObj A X)) := by
  refine ⟨Iso.refl (0 : C), ?_⟩
  apply Iso.ext
  ext <;> simp [translate, RawHom.id, swapStabilizerIso,
    stabilizerIso, Category.assoc]

omit [HasZeroObject C] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Translation preserves raw composition modulo change of stabilizer. -/
theorem translate_comp_rel (A : C) {X Y Z : Translation C}
    (f : RawHom X Y) (g : RawHom Y Z) :
    (f.comp g).translate A |>.Rel
      ((f.translate A).comp (g.translate A)) := by
  refine ⟨Iso.refl (g.stabilizer ⊞ f.stabilizer), ?_⟩
  change
    (stabilizerIso (Iso.refl (g.stabilizer ⊞ f.stabilizer))
        (A ⊞ X.of)).trans
        ((f.translate A).comp (g.translate A)).hom =
      ((f.comp g).translate A).hom
  rw [stabilizerIso_refl, Iso.refl_trans]
  apply Iso.ext
  change
    (biprod.associator g.stabilizer f.stabilizer
          (A ⊞ X.of)).hom ≫
        biprod.map (𝟙 g.stabilizer)
          ((swapStabilizerIso A f.stabilizer X.of).hom ≫
            biprod.map (𝟙 A) f.hom.hom) ≫
        (swapStabilizerIso A g.stabilizer Y.of).hom ≫
        biprod.map (𝟙 A) g.hom.hom =
      (swapStabilizerIso A (g.stabilizer ⊞ f.stabilizer) X.of).hom ≫
        biprod.map (𝟙 A)
          ((biprod.associator g.stabilizer f.stabilizer X.of).hom ≫
            biprod.map (𝟙 g.stabilizer) f.hom.hom ≫
            g.hom.hom)
  rw [biprodMap_id_comp]
  simp only [Category.assoc]
  rw [swapStabilizerIso_natural_hom_assoc]
  rw [swapStabilizerIso_hexagon_hom_assoc]
  rw [← biprodMap_id_comp, ← biprodMap_id_comp]

/-- Raw canonical arrow from `X` to its translation by `A`. -/
noncomputable def diagonalAdd (A : C) (X : Translation C) :
    RawHom X (translateObj A X) where
  stabilizer := A
  hom := Iso.refl _

omit [HasZeroObject C] in
/-- Raw naturality of the canonical arrow into a translation. -/
theorem diagonalAdd_naturality_rel (A : C) {X Y : Translation C}
    (f : RawHom X Y) :
    ((diagonalAdd A X).comp (f.translate A)).Rel
      (f.comp (diagonalAdd A Y)) := by
  refine ⟨biprod.braiding f.stabilizer A, ?_⟩
  simpa [diagonalAdd, translate, RawHom.comp] using
    diagonalAddCoordinateIso A f.stabilizer X.of Y.of f.hom

end RawHom

/-- Translation on quotient arrows. -/
noncomputable def Hom.translate (A : C) {X Y : Translation C} :
    Hom X Y → Hom (translateObj A X) (translateObj A Y) :=
  Quotient.map (RawHom.translate A)
    (fun _ _ h => RawHom.translate_rel A h)

/-- Left translation by `A` on the one-coordinate translation category. -/
noncomputable def translateFunctor (A : C) :
    Translation C ⥤ Translation C where
  obj := translateObj A
  map := Hom.translate A
  map_id X := Quotient.sound (RawHom.translate_id_rel A X)
  map_comp f g := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    exact Quotient.sound (RawHom.translate_comp_rel A _ _)

@[simp]
theorem translateFunctor_obj (A : C) (X : Translation C) :
    (translateFunctor A).obj X = translateObj A X :=
  rfl

@[simp]
theorem translateFunctor_map_mk (A : C) {X Y : Translation C}
    (f : RawHom X Y) :
    (translateFunctor A).map (Hom.mk f) = Hom.mk (f.translate A) :=
  rfl

/-- Canonical arrow from an object to its left translation. -/
noncomputable def diagonalAddHom (A : C) (X : Translation C) :
    X ⟶ translateObj A X :=
  Hom.mk (RawHom.diagonalAdd A X)

/-- The canonical arrows into left translations form a natural
transformation. -/
noncomputable def diagonalAddNatTrans (A : C) :
    Functor.id (Translation C) ⟶
      translateFunctor A where
  app X := diagonalAddHom A X
  naturality {X Y} f := by
    induction f using Quotient.inductionOn with
    | _ f =>
        exact (Quotient.sound
          (RawHom.diagonalAdd_naturality_rel A f)).symm

@[simp]
theorem diagonalAddNatTrans_app (A : C) (X : Translation C) :
    (diagonalAddNatTrans A).app X = diagonalAddHom A X :=
  rfl

end Translation

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- First-coordinate translation and base translation commute through the
projection by an identity-component natural isomorphism. -/
noncomputable def translateFirstProjectionIso (A : C) :
    translateFirstFunctor A ⋙ translationProjection ≅
      translationProjection ⋙ Translation.translateFunctor A :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    induction f using Quotient.inductionOn
    simp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom,
      Translation.translateFunctor, translateFirstFunctor,
      translationProjection, Category.comp_id, Category.id_comp]
    rfl)

@[simp]
theorem translateFirstProjectionIso_hom_app (A : C) (X : Pair C) :
    (translateFirstProjectionIso A).hom.app X = 𝟙 _ :=
  rfl

/-- First-coordinate translation on additive `S⁻¹S` strictly covers
left translation of the one-coordinate base. -/
theorem translateFirstFunctor_comp_translationProjection (A : C) :
    translateFirstFunctor A ⋙ translationProjection =
      translationProjection ⋙ Translation.translateFunctor A :=
  Functor.ext_of_iso (translateFirstProjectionIso A)
    (fun _ => rfl) (fun _ => rfl)

end SInverseS
end CategoryTheory

end

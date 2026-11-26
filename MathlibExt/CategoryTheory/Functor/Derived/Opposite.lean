/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Opposite categories and derived-functor universal properties

Let L : C ⥤ D, F : C ⥤ H and RF : D ⥤ H, with α : F → L ⋙ RF. If RF is a left Kan extension
along α, taking opposites gives β : L.op ⋙ RF.op → F.op, using the inverse composition
comparison followed by α.op. The initial left-extension universal property becomes a terminal
right-extension universal property.

Thus RF.op is a right Kan extension along β. When L localizes a morphism property W and RF is
a right derived functor of F, opposite localization makes RF.op a left derived functor of F.op
along W.op. All three category object and morphism universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uC vC uD vD uH vH

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] {H : Type uH} [Category.{vH} H]
  {L : C ⥤ D} {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)

/-- Terminal opposite extension of an initial left Kan extension.

For α : F → L ⋙ RF with RF a left Kan extension, the right extension with functor RF.op and
map β = (Functor.opComp L RF).inv ≫ NatTrans.op α is universal. Opposites turn its original
unique extension morphisms into unique maps to this terminal right extension. -/
def leftKanUniversalOp [RF.IsLeftKanExtension α] :
    (RightExtension.mk RF.op ((Functor.opComp L RF).inv ≫ NatTrans.op α)).IsUniversal := by
  let original (E : RightExtension L.op F.op) : F ⟶ L ⋙ E.left.unop :=
    { app X := (E.hom.app (op X)).unop
      naturality {X Y} f := by
        exact (congrArg Quiver.Hom.unop (E.hom.naturality f.op)).symm }
  let lift (E : RightExtension L.op F.op) :
      E ⟶ RightExtension.mk RF.op ((Functor.opComp L RF).inv ≫ NatTrans.op α) :=
    CostructuredArrow.homMk
      (NatTrans.op (RF.descOfIsLeftKanExtension α E.left.unop (original E))) (by
        apply NatTrans.ext
        funext X
        simp only [NatTrans.comp_app]
        dsimp only [RightExtension.mk, CostructuredArrow.mk, whiskeringLeft, Functor.opComp,
          NatTrans.op, whiskerLeft, Functor.op, CostructuredArrow.hom, Comma.hom, Iso.refl]
        simp only [NatTrans.comp_app, NatTrans.id_app]
        apply Quiver.Hom.unop_inj
        simp only [unop_comp, Quiver.Hom.unop_op, unop_id_op, Category.comp_id]
        change α.app (unop X) ≫
            (RF.descOfIsLeftKanExtension α E.left.unop (original E)).app (L.obj (unop X)) =
          (E.hom.app X).unop
        exact RF.descOfIsLeftKanExtension_fac_app α E.left.unop (original E) (unop X))
  refine IsTerminal.ofUniqueHom lift ?_
  intro E m
  apply CostructuredArrow.hom_ext
  let γ : RF ⟶ E.left.unop :=
    { app X := (m.left.app (op X)).unop
      naturality {X Y} f := by
        exact (congrArg Quiver.Hom.unop (m.left.naturality f.op)).symm }
  let δ := RF.descOfIsLeftKanExtension α E.left.unop (original E)
  have hm : α ≫ whiskerLeft L γ = original E := by
    apply NatTrans.ext
    funext X
    have h := congrArg Quiver.Hom.unop
      (NatTrans.congr_app (CostructuredArrow.w m) (op X))
    simp only [NatTrans.comp_app] at h
    dsimp only [RightExtension.mk, CostructuredArrow.mk, whiskeringLeft, Functor.opComp,
      NatTrans.op, whiskerLeft, Functor.op, CostructuredArrow.hom, Comma.hom, Iso.refl] at h
    simp only [NatTrans.comp_app, NatTrans.id_app, unop_comp,
      Quiver.Hom.unop_op, unop_id_op, Category.comp_id] at h
    change α.app X ≫ γ.app (L.obj X) = (original E).app X at h
    exact h
  have hδ : α ≫ whiskerLeft L δ = original E :=
    RF.descOfIsLeftKanExtension_fac α E.left.unop (original E)
  have h : γ = δ := RF.hom_ext_of_isLeftKanExtension α γ δ (hm.trans hδ.symm)
  apply NatTrans.ext
  funext X
  apply Quiver.Hom.unop_inj
  exact NatTrans.congr_app h (unop X)

/-- Right Kan extension obtained by taking opposites.

If RF is a left Kan extension of F along α : F → L ⋙ RF, then RF.op is a right Kan extension
of F.op along β : L.op ⋙ RF.op → F.op, with β the opposite of α after the composition
identification. -/
theorem isRightKanExtension_op [RF.IsLeftKanExtension α] :
    RF.op.IsRightKanExtension ((Functor.opComp L RF).inv ≫ NatTrans.op α) :=
  ⟨⟨leftKanUniversalOp RF α⟩⟩

/-- Opposite transport from a right derived functor to a left derived functor.

Let L : C ⥤ D localize W and RF : D ⥤ H be a right derived functor with α : F → L ⋙ RF. Then
RF.op is a left derived functor along W.op, with comparison (Functor.opComp L RF).inv ≫
NatTrans.op α. The result uses opposite localization and the dual Kan-extension universal
property. -/
theorem isLeftDerivedFunctor_op_of_isRightDerived (W : MorphismProperty C)
    [L.IsLocalization W] [RF.IsRightDerivedFunctor α W] :
    RF.op.IsLeftDerivedFunctor ((Functor.opComp L RF).inv ≫ NatTrans.op α) W.op := by
  let : RF.IsLeftKanExtension α := IsRightDerivedFunctor.isLeftKanExtension RF α W
  exact ⟨isRightKanExtension_op RF α⟩

end CategoryTheory.Functor

end

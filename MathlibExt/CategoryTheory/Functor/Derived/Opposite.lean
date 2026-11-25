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
# Opposite transport of a genuine derived-functor universal property

The native left Kan extension has actual universal morphisms and their
uniqueness theorem. Taking their opposites constructs a terminal right
extension. Together with native opposite localization, this turns a right
derived functor into a left derived functor. No new resolution or derived
functor construction is introduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uC vC uD vD uH vH

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] {H : Type uH} [Category.{vH} H]
  {L : C ⥤ D} {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)

/-- The actual opposite universal morphisms turn a native initial extension into a terminal extension. -/
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

/-- A genuine left Kan extension becomes a right Kan extension in the opposite categories. -/
theorem isRightKanExtension_op [RF.IsLeftKanExtension α] :
    RF.op.IsRightKanExtension ((Functor.opComp L RF).inv ≫ NatTrans.op α) :=
  ⟨⟨leftKanUniversalOp RF α⟩⟩

/-- Native opposite localization carries a right derived functor to a left derived functor. -/
theorem isLeftDerivedFunctor_op_of_isRightDerived (W : MorphismProperty C)
    [L.IsLocalization W] [RF.IsRightDerivedFunctor α W] :
    RF.op.IsLeftDerivedFunctor ((Functor.opComp L RF).inv ≫ NatTrans.op α) W.op := by
  let : RF.IsLeftKanExtension α := IsRightDerivedFunctor.isLeftKanExtension RF α W
  exact ⟨isRightKanExtension_op RF α⟩

end CategoryTheory.Functor

end

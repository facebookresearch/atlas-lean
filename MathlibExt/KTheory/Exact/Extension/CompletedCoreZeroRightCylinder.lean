/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroBaseNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanHomotopy
public import MathlibExt.CategoryTheory.FiberedCategory.FiberToStructuredArrow

/-!
# The WHOLE original right-comma cylinder restricted to the zero fiber

Use the SAME original zero-fiber/comma/opposite functor and the actual
right-comma arrow transformation behind the full original comparison.
Its entire classifier is constant at the original opposite Q-zero object.
The resulting original simplicial cylinder is constant on EVERY chain,
without collapsing any completed-Core arrow or component.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory Opposite
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC uObj vObj wHom

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private def actualOriginalRightCommaIndex :
    (SInverse (Core C) (Core C))ᵒᵖ ⥤
      CostructuredArrow (ExtensionCategory.localizedTarget (C := C)).op
        (op (⟨(0 : C)⟩ : QuillenQ C)) :=
  (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
    Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)).op ⋙
    StructuredArrow.toCostructuredArrow (ExtensionCategory.localizedTarget (C := C))
      (⟨(0 : C)⟩ : QuillenQ C)

/-- The SAME original zero-fiber/comma functor followed by its original opposite right-comma
  functor. -/
public def completedCoreOriginalRightCommaFunctor :
    (SInverse (Core C) (Core C))ᵒᵖ ⥤
      CostructuredArrow (ExtensionCategory.localizedTarget (C := C)).op
        (op (⟨(0 : C)⟩ : QuillenQ C)) :=
  actualOriginalRightCommaIndex (C := C)

private theorem actualOriginalRightBaseObject (a : (SInverse (Core C) (Core C))ᵒᵖ) :
    (ExtensionCategory.localizedTarget (C := C)).op.obj
        ((completedCoreOriginalRightCommaFunctor (C := C)).obj a).left =
      op (⟨(0 : C)⟩ : QuillenQ C) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let q := (⟨(0 : C)⟩ : QuillenQ C)
  let z := (FixedTargetExtension.localizedFiberFunctor (0 : C)).obj
    ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a.unop)
  let c := (Functor.fiberToStructuredArrow (p := p) q).obj z
  have hRight : c.right = z.val := Functor.fiberToStructuredArrow_obj_right (p := p) q z
  change op (p.obj c.right) = op q
  exact congrArg op ((congrArg p.obj hRight).trans z.property)

private theorem actualOppositeQArrowHEqZero
    {A B : (QuillenQ C)ᵒᵖ}
    (hA : A = op (⟨(0 : C)⟩ : QuillenQ C))
    (hB : B = op (⟨(0 : C)⟩ : QuillenQ C)) (f : A ⟶ B) :
    HEq f (𝟙 (op (⟨(0 : C)⟩ : QuillenQ C))) := by
  cases hA
  cases hB
  have h : f.unop = (𝟙 (⟨(0 : C)⟩ : QuillenQ C)) :=
    QuillenQ.hom_eq_of_target_isZero f.unop (𝟙 _) (isZero_zero C)
  exact heq_of_eq (congrArg Quiver.Hom.op h)

private theorem actualOriginalRightZeroClassifier :
    let p := ExtensionCategory.localizedTarget (C := C)
    let q := (⟨(0 : C)⟩ : QuillenQ C)
    NatTrans.nerveCylinderFunctor (Functor.whiskerLeft
      (completedCoreOriginalRightCommaFunctor (C := C))
      (SSet.rightCommaArrowNatTrans.{uC, 0, max uC vC} p.op (op q))) =
      (Functor.const ((SInverse (Core C) (Core C))ᵒᵖ × Fin 2)).obj (op q) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let q := (⟨(0 : C)⟩ : QuillenQ C)
  let J := completedCoreOriginalRightCommaFunctor (C := C)
  let alpha := Functor.whiskerLeft J
    (SSet.rightCommaArrowNatTrans.{uC, 0, max uC vC} p.op (op q))
  have hObject (a : (SInverse (Core C) (Core C))ᵒᵖ) (i : Fin 2) :
      (NatTrans.nerveCylinderFunctor alpha).obj (a, i) = op q := by
    fin_cases i
    · exact (NatTrans.nerveCylinderFunctor_obj_zero alpha a).trans
        (actualOriginalRightBaseObject a)
    · exact NatTrans.nerveCylinderFunctor_obj_one alpha a
  refine CategoryTheory.Functor.hext (fun x => hObject x.1 x.2) ?_
  rintro ⟨a, i⟩ ⟨b, j⟩ f
  exact actualOppositeQArrowHEqZero (hObject a i) (hObject b j)
    ((NatTrans.nerveCylinderFunctor alpha).map f)

/-- The ENTIRE actual original restricted right-comma classifier is the original constant Q-zero. -/
public theorem completedCoreOriginalRightCommaCylinder_eq_const :
    let p := ExtensionCategory.localizedTarget (C := C)
    let q := (⟨(0 : C)⟩ : QuillenQ C)
    NatTrans.nerveCylinderFunctor (Functor.whiskerLeft
      (completedCoreOriginalRightCommaFunctor (C := C))
      (SSet.rightCommaArrowNatTrans.{uC, 0, max uC vC} p.op (op q))) =
      (Functor.const ((SInverse (Core C) (Core C))ᵒᵖ × Fin 2)).obj (op q) :=
  actualOriginalRightZeroClassifier (C := C)

private theorem actualCommonDownCylinderUpPrecomposition
    {X B : Type uObj} [Category.{max vObj wHom} X] [Category.{max vObj wHom} B]
    {A : Type (max uObj vObj)} [Category.{max vObj wHom} A]
    {F G : A ⥤ B} (K : X ⥤ A) (alpha : F ⟶ G) :
    (nerveMapCommonHomUp.{uObj, vObj, wHom} K ▷ (Δ[1] : SSet.{max uObj vObj wHom})) ≫
      (NatTrans.nerveHomotopyCommonHom.{uObj, vObj, wHom} alpha).h =
        (NatTrans.nerveHomotopy (Functor.whiskerLeft K alpha)).h := by
  ext Delta x
  let up := nerveMapCommonHomUp.{uObj, vObj, wHom} K
  let z : (nerve X).obj Delta ×
      (Δ[1] : SSet.{max uObj vObj wHom}).obj Delta := x
  let y : (nerve A).obj Delta ×
      (Δ[1] : SSet.{max uObj vObj wHom}).obj Delta :=
    (up.app Delta z.1, z.2)
  have hPoint : (up ▷ (Δ[1] : SSet.{max uObj vObj wHom})).app Delta x = y :=
    (congrArg (fun f : (nerve X).obj Delta ⊗
        (Δ[1] : SSet.{max uObj vObj wHom}).obj Delta ⟶
        (nerve A).obj Delta ⊗ (Δ[1] : SSet.{max uObj vObj wHom}).obj Delta =>
      f z) (CategoryTheory.Monoidal.whiskerRight_app
        (α := up) (F' := (Δ[1] : SSet.{max uObj vObj wHom})) (X := Delta))).trans
      (CategoryTheory.whiskerRight_apply (up.app Delta)
        ((Δ[1] : SSet.{max uObj vObj wHom}).obj Delta) z)
  have hCommon := NatTrans.nerveHomotopyCommonHom_h_app_value.{uObj, vObj, wHom}
    alpha Delta y
  let c : ComposableArrows (X × Fin 2) Delta.unop.len :=
    z.1.prod' (SSet.stdSimplex.asOrderHom z.2).toFunctor
  have hInput : y.1.prod' (SSet.stdSimplex.asOrderHom y.2).toFunctor =
      c ⋙ (K.prod (𝟭 (Fin 2))) :=
    congrArg (fun d : (nerve A).obj Delta =>
      d.prod' (SSet.stdSimplex.asOrderHom z.2).toFunctor)
        (nerveMapCommonHomUp_app.{uObj, vObj, wHom} K Delta z.1)
  have hInputValue := congrArg
    (fun d : ComposableArrows (A × Fin 2) Delta.unop.len =>
      ((NatTrans.nerveCylinderFunctor alpha).mapComposableArrows Delta.unop.len).obj d)
        hInput
  have hClassifier := congrArg
    (fun L : X × Fin 2 ⥤ B => (L.mapComposableArrows Delta.unop.len).obj c)
      (NatTrans.nerveCylinderFunctor_whiskerLeft K alpha)
  have hPlainApp := NatTrans.nerveHomotopyMap_app_value
    (Functor.whiskerLeft K alpha) Delta x
  have hPlainField := congrArg
    (fun h : nerve X ⊗ (Δ[1] : SSet.{max uObj vObj wHom}) ⟶ nerve B =>
      h.app Delta x)
        (NatTrans.nerveHomotopy_h_value (Functor.whiskerLeft K alpha))
  exact (congrArg
    (fun d : (nerve A).obj Delta × (Δ[1] : SSet.{max uObj vObj wHom}).obj Delta =>
      (NatTrans.nerveHomotopyCommonHom.{uObj, vObj, wHom} alpha).h.app Delta d)
        hPoint).trans
          (hCommon.trans (hInputValue.trans
            (hClassifier.symm.trans (hPlainApp.symm.trans hPlainField.symm))))

private theorem actualOriginalRestrictedRightCylinderConst :
    let p := ExtensionCategory.localizedTarget (C := C)
    let q := (⟨(0 : C)⟩ : QuillenQ C)
    (nerveMapCommonHomUp.{uC, max uC vC, 0}
        (completedCoreOriginalRightCommaFunctor (C := C)) ▷
          (Δ[1] : SSet.{max uC vC})) ≫
      (SSet.rightCommaArrowNerveHomotopy.{uC, 0, max uC vC} p.op (op q)).h =
        SSet.const (ComposableArrows.mk₀ (op q)) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let q := (⟨(0 : C)⟩ : QuillenQ C)
  let J := completedCoreOriginalRightCommaFunctor (C := C)
  let alpha := SSet.rightCommaArrowNatTrans.{uC, 0, max uC vC} p.op (op q)
  have hUpDown := actualCommonDownCylinderUpPrecomposition J alpha
  have hRight := congrArg (fun h =>
      (nerveMapCommonHomUp.{uC, max uC vC, 0} J ▷
        (Δ[1] : SSet.{max uC vC})) ≫ h)
    (SSet.rightCommaArrowNerveHomotopy_h_value.{uC, 0, max uC vC} p.op (op q))
  have hConst : (NatTrans.nerveHomotopy (Functor.whiskerLeft J alpha)).h =
      SSet.const (ComposableArrows.mk₀ (op q)) := by
    ext Delta x
    let z : (nerve ((SInverse (Core C) (Core C))ᵒᵖ)).obj Delta ×
        (Δ[1] : SSet.{max uC vC}).obj Delta := x
    have hField := congrArg
      (fun h : nerve ((SInverse (Core C) (Core C))ᵒᵖ) ⊗
          (Δ[1] : SSet.{max uC vC}) ⟶ nerve ((QuillenQ C)ᵒᵖ) =>
        h.app Delta x)
      (NatTrans.nerveHomotopy_h_value (Functor.whiskerLeft J alpha))
    have hApp := NatTrans.nerveHomotopyMap_app_value
      (Functor.whiskerLeft J alpha) Delta x
    have hClassifier := completedCoreOriginalRightCommaCylinder_eq_const (C := C)
    have hChain := congrArg
      (fun L : (SInverse (Core C) (Core C))ᵒᵖ × Fin 2 ⥤ (QuillenQ C)ᵒᵖ =>
        (L.mapComposableArrows Delta.unop.len).obj
          (z.1.prod' (SSet.stdSimplex.asOrderHom z.2).toFunctor)) hClassifier
    exact hField.trans (hApp.trans (hChain.trans (by rfl)))
  exact hRight.trans (hUpDown.trans hConst)

/-- The WHOLE original right-comma H.h restricted along the actual zero-fiber index is constant on
  EVERY chain. -/
public theorem completedCoreOriginalRightCommaH_restrict_eq_const :
    let p := ExtensionCategory.localizedTarget (C := C)
    let q := (⟨(0 : C)⟩ : QuillenQ C)
    (nerveMapCommonHomUp.{uC, max uC vC, 0}
        (completedCoreOriginalRightCommaFunctor (C := C)) ▷
          (Δ[1] : SSet.{max uC vC})) ≫
      (SSet.rightCommaArrowNerveHomotopy.{uC, 0, max uC vC} p.op (op q)).h =
        SSet.const (ComposableArrows.mk₀ (op q)) :=
  actualOriginalRestrictedRightCylinderConst (C := C)

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# Whole original right-comma index value

The proper owned recipe retains the exact original zero/fiber/comma and
opposite right-comma functor, with all original cylinder choices.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory Opposite
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uRightIndex vRightIndex

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type uRightIndex} [Category.{vRightIndex} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem originalRightCommaIndexWholeValue :
    completedCoreOriginalRightCommaFunctor (C := C) =
      (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)).op ⋙
      StructuredArrow.toCostructuredArrow (ExtensionCategory.localizedTarget (C := C))
        (⟨(0 : C)⟩ : QuillenQ C) := rfl

/-- The SAME named right-comma index has its whole original zero/fiber/comma/opposite recipe. -/
public theorem completedCoreOriginalRightCommaFunctor_value :
    completedCoreOriginalRightCommaFunctor (C := C) =
      (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (0 : C) ⋙
        Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)).op ⋙
      StructuredArrow.toCostructuredArrow (ExtensionCategory.localizedTarget (C := C))
        (⟨(0 : C)⟩ : QuillenQ C) :=
  originalRightCommaIndexWholeValue (C := C)

end AlgebraicKTheory.OriginalQZeroComparison

end

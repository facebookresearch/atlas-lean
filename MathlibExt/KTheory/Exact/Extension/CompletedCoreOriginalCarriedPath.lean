/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedCoreZeroRightPath
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaQuillenB
public import MathlibExt.CategoryTheory.ComposableArrows.Opposite

/-!
# EVERY-point constant carried path in the ORIGINAL full zero fiber

The exact original zero/comma/opposite index intertwines the full original
left and right comparison source maps. Realization-reversal naturality
preserves this whole square. The original opposite right-fiber carried path
is constant at every source point/time and is transported to the original
chosen Q-zero vertex. The original total coordinate and all completed
components remain unrestricted; no fiber map is inferred from projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory Opposite
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem actualOriginalZeroCommaOppositeSource :
    let p := ExtensionCategory.localizedTarget (C := C)
    let q := (⟨(0 : C)⟩ : QuillenQ C)
    SimplicialObject.opFunctor.map (completedCoreToZeroLeftCommaNerveMap (C := C)) ≫
      (SSet.leftCommaOppositeNerveIso.{max uC vC, max uC vC, uC} p (op q)).hom =
    (nerveOppositeSimplicialIso (SInverse (Core C) (Core C))).inv ≫
      nerveMapCommonHomUp.{uC, max uC vC, 0}
        (completedCoreOriginalRightCommaFunctor (C := C)) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let q := (⟨(0 : C)⟩ : QuillenQ C)
  let Z := FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (0 : C)
  let U := Functor.fiberToStructuredArrow (p := p) q
  let L := Z ⋙ U
  have hOriginal : completedCoreToZeroLeftCommaNerveMap (C := C) =
      nerveMapCommonHomUp.{uC, max uC vC, 0} L :=
    (completedCoreToZeroLeftCommaNerveMap_value (C := C)).trans
      (nerveMapCommonHomUp_nerveMap_comp.{uC, max uC vC, 0} Z U)
  rw [hOriginal, completedCoreOriginalRightCommaFunctor_value]
  ext Delta sigma
  obtain ⟨⟨n⟩⟩ := Delta
  let K : SSet.{max uC vC} := nerve (SInverse (Core C) (Core C))
  let A : SSet.{max uC vC} := nerve (StructuredArrow q p)
  let B : SSet.{max uC vC} := nerve (CostructuredArrow p.op (op q))
  let up : K ⟶ A := nerveMapCommonHomUp.{uC, max uC vC, 0} L
  let eK : (SimplicialObject.opFunctor.obj K).obj (op ⦋n⦌) ≅ K.obj (op ⦋n⦌) :=
    SimplicialObject.opObjIso
  let eA : (SimplicialObject.opFunctor.obj A).obj (op ⦋n⦌) ≅ A.obj (op ⦋n⦌) :=
    SimplicialObject.opObjIso
  let s : ComposableArrows (SInverse (Core C) (Core C)) n := eK.hom sigma
  let O : SimplicialObject.opFunctor.obj A ≅ B :=
    SSet.leftCommaOppositeNerveIso.{max uC vC, max uC vC, uC} p (op q)
  let cO : nerve ((SInverse (Core C) (Core C))ᵒᵖ) ≅
      SimplicialObject.opFunctor.obj K :=
    nerveOppositeSimplicialIso (SInverse (Core C) (Core C))
  let right : nerve ((SInverse (Core C) (Core C))ᵒᵖ) ⟶ B :=
    nerveMapCommonHomUp.{uC, max uC vC, 0}
      (L.op ⋙ StructuredArrow.toCostructuredArrow p q)
  have hOpPoint : (SimplicialObject.opFunctor.map up).app (op ⦋n⦌) sigma =
      eA.inv ((L.mapComposableArrows n).obj s) :=
    (congrArg
      (fun a : (SimplicialObject.opFunctor.obj K).obj (op ⦋n⦌) ⟶
          (SimplicialObject.opFunctor.obj A).obj (op ⦋n⦌) => a sigma)
      (SimplicialObject.opFunctor_map_app up (op ⦋n⦌))).trans
        ((CategoryTheory.types_comp_apply eK.hom (up.app (op ⦋n⦌) ≫ eA.inv) sigma).trans
          ((CategoryTheory.types_comp_apply (up.app (op ⦋n⦌)) eA.inv s).trans
            (congrArg eA.inv (nerveMapCommonHomUp_app.{uC, max uC vC, 0}
              L (op ⦋n⦌) s))))
  have hLeftRaw : O.hom.app (op ⦋n⦌) (eA.inv ((L.mapComposableArrows n).obj s)) =
      ((L.mapComposableArrows n).obj s).op ⋙ StructuredArrow.toCostructuredArrow p q :=
    SSet.leftCommaOppositeNerveIso_hom_app_mk.{max uC vC, max uC vC, uC}
      p (op q) n ((L.mapComposableArrows n).obj s)
  have hLeft : (SimplicialObject.opFunctor.map up ≫ O.hom).app (op ⦋n⦌) sigma =
      ((L.mapComposableArrows n).obj s).op ⋙ StructuredArrow.toCostructuredArrow p q :=
    (congrArg
      (fun a : (SimplicialObject.opFunctor.obj K).obj (op ⦋n⦌) ⟶ B.obj (op ⦋n⦌) =>
        a sigma)
      (SSet.comp_app (SimplicialObject.opFunctor.map up) O.hom (op ⦋n⦌))).trans
        ((CategoryTheory.types_comp_apply
          ((SimplicialObject.opFunctor.map up).app (op ⦋n⦌)) (O.hom.app (op ⦋n⦌)) sigma).trans
            ((congrArg (fun a : (SimplicialObject.opFunctor.obj A).obj (op ⦋n⦌) =>
              O.hom.app (op ⦋n⦌) a) hOpPoint).trans hLeftRaw))
  have hRaw : eK.inv s = sigma :=
    (CategoryTheory.types_comp_apply eK.hom eK.inv sigma).symm.trans
      (ConcreteCategory.congr_hom eK.hom_inv_id sigma)
  have hInverse : cO.inv.app (op ⦋n⦌) sigma = s.op :=
    (congrArg (fun a : (SimplicialObject.opFunctor.obj K).obj (op ⦋n⦌) =>
      cO.inv.app (op ⦋n⦌) a) hRaw.symm).trans
        (nerveOppositeSimplicialIso_inv_app_mk (SInverse (Core C) (Core C)) n s)
  have hRight : (cO.inv ≫ right).app (op ⦋n⦌) sigma =
      (s.op ⋙ L.op) ⋙ StructuredArrow.toCostructuredArrow p q :=
    (congrArg
      (fun a : (SimplicialObject.opFunctor.obj K).obj (op ⦋n⦌) ⟶ B.obj (op ⦋n⦌) =>
        a sigma)
      (SSet.comp_app cO.inv right (op ⦋n⦌))).trans
        ((CategoryTheory.types_comp_apply (cO.inv.app (op ⦋n⦌)) (right.app (op ⦋n⦌)) sigma).trans
          ((congrArg (fun a : ComposableArrows ((SInverse (Core C) (Core C))ᵒᵖ) n =>
            right.app (op ⦋n⦌) a) hInverse).trans
              (nerveMapCommonHomUp_app.{uC, max uC vC, 0}
                (L.op ⋙ StructuredArrow.toCostructuredArrow p q) (op ⦋n⦌) s.op)))
  exact hLeft.trans
    ((congrArg (fun a : ComposableArrows ((StructuredArrow q p)ᵒᵖ) n =>
      a ⋙ StructuredArrow.toCostructuredArrow p q)
        (ComposableArrows.op_mapFunctor L n s)).trans hRight.symm)

private theorem actualOriginalZeroCommaRealizedSource :
    let p := ExtensionCategory.localizedTarget (C := C)
    let q := (⟨(0 : C)⟩ : QuillenQ C)
    SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C)) ≫
      (SSet.leftCommaRealizationIso.{uC, 0, max uC vC} p (op q)).hom =
    (SSet.nerveRealizationOppositeIso (SInverse (Core C) (Core C))).inv ≫
      SSet.toTop.map (nerveMapCommonHomUp.{uC, max uC vC, 0}
        (completedCoreOriginalRightCommaFunctor (C := C))) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let q := (⟨(0 : C)⟩ : QuillenQ C)
  let K : SSet.{max uC vC} := nerve (SInverse (Core C) (Core C))
  let A : SSet.{max uC vC} := nerve (StructuredArrow q p)
  let B : SSet.{max uC vC} := nerve (CostructuredArrow p.op (op q))
  let f : K ⟶ A := completedCoreToZeroLeftCommaNerveMap (C := C)
  let O : SimplicialObject.opFunctor.obj A ≅ B :=
    SSet.leftCommaOppositeNerveIso.{max uC vC, max uC vC, uC} p (op q)
  let cO : nerve ((SInverse (Core C) (Core C))ᵒᵖ) ≅
      SimplicialObject.opFunctor.obj K :=
    nerveOppositeSimplicialIso (SInverse (Core C) (Core C))
  let J : nerve ((SInverse (Core C) (Core C))ᵒᵖ) ⟶ B :=
    nerveMapCommonHomUp.{uC, max uC vC, 0}
      (completedCoreOriginalRightCommaFunctor (C := C))
  have hLeftRecipe : (SSet.leftCommaRealizationIso.{uC, 0, max uC vC} p (op q)).hom =
      (SSet.toTopReversalIso A).inv ≫ SSet.toTop.map O.hom :=
    SSet.leftCommaRealizationIso_hom_value.{uC, 0, max uC vC} p (op q)
  have hInverseRecipe : (SSet.nerveRealizationOppositeIso
      (SInverse (Core C) (Core C))).inv =
        (SSet.toTopReversalIso K).inv ≫ SSet.toTop.map cO.inv :=
    SSet.nerveRealizationOppositeIso_inv_value (SInverse (Core C) (Core C))
  have hReverse := SSet.toTopReversalIso_inv_naturality f
  have hOpposite := actualOriginalZeroCommaOppositeSource (C := C)
  calc
    SSet.toTop.map f ≫ (SSet.leftCommaRealizationIso.{uC, 0, max uC vC} p (op q)).hom =
        SSet.toTop.map f ≫ ((SSet.toTopReversalIso A).inv ≫ SSet.toTop.map O.hom) :=
      congrArg (fun a : SSet.toTop.obj A ⟶ SSet.toTop.obj B => SSet.toTop.map f ≫ a)
        hLeftRecipe
    _ = (SSet.toTop.map f ≫ (SSet.toTopReversalIso A).inv) ≫ SSet.toTop.map O.hom :=
      (Category.assoc _ _ _).symm
    _ = ((SSet.toTopReversalIso K).inv ≫
        SSet.toTop.map (SimplicialObject.opFunctor.map f)) ≫ SSet.toTop.map O.hom :=
      congrArg (fun a => a ≫ SSet.toTop.map O.hom) hReverse
    _ = (SSet.toTopReversalIso K).inv ≫
        SSet.toTop.map (SimplicialObject.opFunctor.map f ≫ O.hom) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => (SSet.toTopReversalIso K).inv ≫ a)
          (SSet.toTop.map_comp (SimplicialObject.opFunctor.map f) O.hom).symm)
    _ = (SSet.toTopReversalIso K).inv ≫ SSet.toTop.map (cO.inv ≫ J) :=
      congrArg (fun a => (SSet.toTopReversalIso K).inv ≫ SSet.toTop.map a) hOpposite
    _ = ((SSet.toTopReversalIso K).inv ≫ SSet.toTop.map cO.inv) ≫ SSet.toTop.map J :=
      (congrArg (fun a => (SSet.toTopReversalIso K).inv ≫ a)
        (SSet.toTop.map_comp cO.inv J)).trans (Category.assoc _ _ _).symm
    _ = (SSet.nerveRealizationOppositeIso (SInverse (Core C) (Core C))).inv ≫
        SSet.toTop.map J :=
      congrArg (fun a : SSet.toTop.obj K ⟶
          SSet.toTop.obj (nerve ((SInverse (Core C) (Core C))ᵒᵖ)) => a ≫ SSet.toTop.map J)
        hInverseRecipe.symm

private theorem actualOriginalFullFiberCarriedPath
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C))))
    (t : TopCat.I.{max uC vC}) :
    TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
        (ExtensionCategory.localizedTarget (C := C))))
      (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C)))
      (completedCoreToOriginalHomotopyFiber (C := C) x) t =
    SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C)) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let q := (⟨(0 : C)⟩ : QuillenQ C)
  let a := SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))
  let eL := SSet.leftCommaRealizationIso.{uC, 0, max uC vC} p (op q)
  let eK := SSet.nerveRealizationOppositeIso (SInverse (Core C) (Core C))
  let k := SSet.toTop.map (nerveMapCommonHomUp.{uC, max uC vC, 0}
    (completedCoreOriginalRightCommaFunctor (C := C)))
  let eQ := SSet.nerveRealizationOppositeIso (QuillenQ C)
  let bOp := SSet.realizedVertex
    (X := (nerve ((QuillenQ C)ᵒᵖ) : SSet.{max uC vC})) (ComposableArrows.mk₀ (op q))
  have hSource : eL.hom (a x) = k (eK.inv x) :=
    (TopCat.comp_app a eL.hom x).symm.trans
      ((ConcreteCategory.congr_hom (actualOriginalZeroCommaRealizedSource (C := C)) x).trans
        (TopCat.comp_app eK.inv k x))
  have hPath : TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0} p.op)) bOp
      (SSet.rightCommaHomotopyFiberComparison.{uC, 0, max uC vC} p.op (op q)
        (eL.hom (a x))) t = bOp :=
    (congrArg (fun y => TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0} p.op)) bOp
      (SSet.rightCommaHomotopyFiberComparison.{uC, 0, max uC vC} p.op (op q) y) t) hSource).trans
        (completedCoreOriginalRightFiber_path_const (C := C) (eK.inv x) t)
  exact (completedCoreToOriginalHomotopyFiber_path_apply (C := C) x t).trans
    ((congrArg eQ.hom hPath).trans (SSet.leftCommaBaseVertex_eq q))

/-- EVERY point and time of the SAME ORIGINAL full zero-fiber map carries the literal constant
  Q-zero path. -/
public theorem completedCoreToOriginalHomotopyFiber_path_const
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C))))
    (t : TopCat.I.{max uC vC}) :
    TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
        (ExtensionCategory.localizedTarget (C := C))))
      (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C)))
      (completedCoreToOriginalHomotopyFiber (C := C) x) t =
    SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C)) :=
  actualOriginalFullFiberCarriedPath x t

end AlgebraicKTheory.OriginalQZeroComparison

end

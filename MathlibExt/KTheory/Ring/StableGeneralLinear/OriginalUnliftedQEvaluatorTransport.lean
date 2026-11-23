/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.UniverseLift
public import MathlibExt.KTheory.Ring.StableGeneralLinear.MixedOriginalQRealizationTransport
public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveScalarK0Naturality
public import MathlibExt.KTheory.Waldhausen.K0.Exact

/-!
# Original unlifted Q inverse families and component evaluator transport

The original UniverseLift Qup/Qdown, full Qleft/Qright and retuning choices
are retained. Literal carrier lifts are removed by their actual original
up/down maps. The existing Q/S fundamental/component facade and original
projective generator calibration give evaluator transport on every class.
No Q map is defined by an evaluator or a K0 dictionary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen.SConstruction
open scoped ContinuousMap Simplicial ZeroObject

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] CategoryTheory.ExactCategory.waldhausenCategory

namespace AlgebraicKTheory.OriginalQuillenUnliftedTransport

open AlgebraicKTheory.QuillenQSZigzagGroupNaturality.Internal

private theorem originalQLegComponentFundamentalValue.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (c : ZerothHomotopy (quillenStageGridDiagonalKSpace
      C)) :
    loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C)
        (quillenStageGridToNQPiZeroEquiv C c) =
      quillenStageGridToNQFundamentalMulEquiv C
        (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
          (quillenStageGridDiagonalReal.basepoint C) c) := by
  let E := loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C)
  change E (E.symm (basedFundamentalGroupMap (quillenStageGridToNQWeaklyPointed (C := C)).hom
    (quillenStageGridToNQWeaklyPointed (C := C)).rootPath
    (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
      (quillenStageGridDiagonalReal.basepoint C) c))) = _
  exact E.apply_symm_apply _

private theorem originalStageLegComponentFundamentalValue.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (c : ZerothHomotopy (quillenStageGridDiagonalKSpace
      C)) :
    loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) (quillenStageGridToStagePiZeroEquiv C c) =
      quillenStageGridToStageFundamentalMulEquiv C
        (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
          (quillenStageGridDiagonalReal.basepoint C) c) := by
  let E := loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
    (stageWeakDiagonalReal.basepoint C)
  change E (E.symm (basedFundamentalGroupMap
    (quillenStageGridToStageWeaklyPointed (C := C)).hom
    (quillenStageGridToStageWeaklyPointed (C := C)).rootPath
    (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
      (quillenStageGridDiagonalReal.basepoint C) c))) = _
  exact E.apply_symm_apply _

private theorem originalQComponentFundamentalFacade.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (c : ZerothHomotopy (NQKSpace C)) :
    NQKSpacePiZeroEquivK0 C c = Multiplicative.toAdd
      (NQRealizedFundamentalK0MulEquiv C
        (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C) c)) := by
  let g := (quillenStageGridToNQPiZeroEquiv C).symm c
  have hQ := originalQLegComponentFundamentalValue C g
  rw [show quillenStageGridToNQPiZeroEquiv C g = c from
    (quillenStageGridToNQPiZeroEquiv C).apply_symm_apply c] at hQ
  have hS := originalStageLegComponentFundamentalValue C g
  change Multiplicative.toAdd (stageWeakDiagonalRealizedFundamentalK0MulEquiv C
    (loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
      (stageWeakDiagonalReal.basepoint C) (quillenStageGridToStagePiZeroEquiv C g))) =
    Multiplicative.toAdd (stageWeakDiagonalRealizedFundamentalK0MulEquiv C
      (quillenStageGridToStageFundamentalMulEquiv C
        ((quillenStageGridToNQFundamentalMulEquiv C).symm
          (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C) c))))
  rw [hS, hQ, MulEquiv.symm_apply_apply]

private def originalFundamentalPointEquiv.{uX}
    {X : Type uX} [TopologicalSpace X] {x y : X} (h : x = y) :
    FundamentalGroup X x ≃* FundamentalGroup X y := by
  cases h
  exact MulEquiv.refl _

private theorem originalFundamentalPointEquiv_loop.{uX}
    {X : Type uX} [TopologicalSpace X] {x y : X} (h : x = y) (p : LoopSpace X x) :
    originalFundamentalPointEquiv h
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.cast h.symm h.symm)) := by
  cases h
  rfl

/-- The actual original Q/S dictionary at the literal original Q zero vertex. -/
public def originalQFundamentalK0Equiv.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    Additive (FundamentalGroup (NQReal C) (OriginalQZeroComparison.zeroQVertex (C := C))) ≃+
      K0 C :=
  ((originalFundamentalPointEquiv (NQReal.basepoint_eq_realizedVertex C).symm).trans
    ((NQRealizedFundamentalK0MulEquiv C).trans
      (Iso.addCommGroupIsoToAddEquiv (WaldhausenKTheory.K0.exactIso
        C)).toMultiplicative)).toAdditive

/-- EVERY original loop has the same canonical exact-K0 value under the public facade. -/
public theorem originalQFundamentalK0Equiv_loop.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (p : BasedSplitExactQLoop.originalQLoops (C := C)) :
    originalQFundamentalK0Equiv C
        (Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) =
      OriginalQK0Comparison.canonicalLoopComponentsK0 (C := C) (ZerothHomotopy.mk p) := by
  let q := p.cast (NQReal.basepoint_eq_realizedVertex C)
    (NQReal.basepoint_eq_realizedVertex C)
  have hPoint := originalFundamentalPointEquiv_loop
    (NQReal.basepoint_eq_realizedVertex C).symm p
  have hFacade := originalQComponentFundamentalFacade C (ZerothHomotopy.mk q)
  have hLoop := loopComponentsEquivFundamentalGroup_mk (X := NQReal C)
    (x := NQReal.basepoint C) q
  have hValue := (congrArg (fun g => WaldhausenKTheory.K0.toExact C
    (Multiplicative.toAdd (NQRealizedFundamentalK0MulEquiv C g))) hPoint)
  have hEvaluate := (congrArg (WaldhausenKTheory.K0.toExact C) hFacade).trans
    (congrArg (fun g => WaldhausenKTheory.K0.toExact C
      (Multiplicative.toAdd (NQRealizedFundamentalK0MulEquiv C g))) hLoop)
  exact hValue.trans (hEvaluate.symm.trans
    (OriginalQK0Comparison.canonicalLoopComponentsK0_mk (C := C) p).symm)

private def actualLoopComponentsMap.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun {_ _} p => ZerothHomotopy.sound (p.map f.continuous))

private theorem actualLoopComponentsMap_mk.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    actualLoopComponentsMap f (ZerothHomotopy.mk x) = ZerothHomotopy.mk (f x) := by
  rfl

/-- The original Qdown with ONLY its literal native carrier lift removed. -/
public def originalUnliftedQdown.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : C(QuillenUniverseLift.originalLoops.{uR, uM, uObj, uHom} R,
    QuillenUniverseLift.canonicalLoops.{uR, uM} R) :=
  (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R).comp
    (QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R)

/-- The actual original Qup with the SAME literal carrier descent. -/
public def originalUnliftedQup.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : C(QuillenUniverseLift.canonicalLoops.{uR, uM} R,
    QuillenUniverseLift.originalLoops.{uR, uM, uObj, uHom} R) :=
  (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
    (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R)

/-- The original literal source and target constant loops remain unchanged. -/
public theorem originalUnliftedQmap_roots.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] :
    originalUnliftedQdown.{uR, uM, uObj, uHom, uNative} R
      (QuillenUniverseLift.originalConstantLoop.{uR, uM, uObj, uHom} R) =
      QuillenUniverseLift.canonicalConstantLoop.{uR, uM} R ∧
    originalUnliftedQup.{uR, uM, uObj, uHom, uNative} R
      (QuillenUniverseLift.canonicalConstantLoop.{uR, uM} R) =
      QuillenUniverseLift.originalConstantLoop.{uR, uM, uObj, uHom} R :=
  ⟨(congrArg (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R)
      (QuillenUniverseLift.rawNativeCarrierUp_constant.{uR, uM, uObj, uHom, uNative} R)).trans
        (QuillenUniverseLift.Qdown_constant.{uR, uM, uObj, uHom, uNative} R),
    (congrArg (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R)
      (QuillenUniverseLift.Qup_constant.{uR, uM, uObj, uHom, uNative} R)).trans
        (QuillenUniverseLift.rawNativeCarrierDown_constant.{uR, uM, uObj, uHom, uNative} R)⟩

/-- The ENTIRE original left inverse family is transported by literal carrier maps. -/
public def originalUnliftedQleftFamily.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ContinuousMap.HomotopyRel
    ((originalUnliftedQup.{uR, uM, uObj, uHom, uNative} R).comp (originalUnliftedQdown.{uR, uM,
      uObj, uHom, uNative} R))
    (ContinuousMap.id (QuillenUniverseLift.originalLoops.{uR, uM, uObj, uHom} R))
    {QuillenUniverseLift.originalConstantLoop.{uR, uM, uObj, uHom} R} := by
  let up := QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R
  let down := QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R
  let H := ((QuillenUniverseLift.QleftHomotopyRel.{uR, uM, uObj, uHom, uNative}
    R).precomposePointRelative up
    (QuillenUniverseLift.originalConstantLoop.{uR, uM, uObj, uHom} R)
    (QuillenUniverseLift.rawNativeCarrierUp_constant.{uR, uM, uObj, uHom, uNative}
      R)).compContinuousMap down
  refine H.cast (by apply ContinuousMap.ext; intro p; rfl) ?_
  apply ContinuousMap.ext
  intro p
  exact congrArg (fun f => f p) (QuillenUniverseLift.rawNativeCarrierDown_comp_up.{uR, uM, uObj,
    uHom, uNative} R)

/-- The ENTIRE original right inverse family retains the exact original target root. -/
public def originalUnliftedQrightFamily.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ContinuousMap.HomotopyRel
    ((originalUnliftedQdown.{uR, uM, uObj, uHom, uNative} R).comp (originalUnliftedQup.{uR, uM,
      uObj, uHom, uNative} R))
    (ContinuousMap.id (QuillenUniverseLift.canonicalLoops.{uR, uM} R))
    {QuillenUniverseLift.canonicalConstantLoop.{uR, uM} R} := by
  let up := QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R
  let down := QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R
  refine (QuillenUniverseLift.QrightHomotopyRel.{uR, uM, uObj, uHom, uNative} R).cast ?_ rfl
  apply ContinuousMap.ext
  intro p
  exact (congrArg (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R)
    (congrArg (fun f => f (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R p))
      (QuillenUniverseLift.rawNativeCarrierUp_comp_down.{uR, uM, uObj, uHom, uNative} R))).symm

/-- BOTH transported full families fix the SAME original constant loops at EVERY time. -/
public theorem originalUnliftedQfamily_roots.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] (t : unitInterval) :
    originalUnliftedQleftFamily.{uR, uM, uObj, uHom, uNative} R
        (t, QuillenUniverseLift.originalConstantLoop.{uR, uM, uObj, uHom} R) =
        QuillenUniverseLift.originalConstantLoop.{uR, uM, uObj, uHom} R ∧
      originalUnliftedQrightFamily.{uR, uM, uObj, uHom, uNative} R
        (t, QuillenUniverseLift.canonicalConstantLoop.{uR, uM} R) =
        QuillenUniverseLift.canonicalConstantLoop.{uR, uM} R :=
  ⟨(originalUnliftedQleftFamily.{uR, uM, uObj, uHom, uNative} R).eq_snd t (by rfl),
    (originalUnliftedQrightFamily.{uR, uM, uObj, uHom, uNative} R).eq_snd t (by rfl)⟩

/-- The actual unlifted component action is induced by its original continuous map. -/
public def originalUnliftedQdownComponents.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ZerothHomotopy (QuillenUniverseLift.originalLoops.{uR, uM, uObj, uHom}
      R) →
    ZerothHomotopy (QuillenUniverseLift.canonicalLoops.{uR, uM} R) :=
  actualLoopComponentsMap (originalUnliftedQdown.{uR, uM, uObj, uHom, uNative} R)

/-- The original unlifted Q inclusion acts on EVERY original loop component. -/
public def originalUnliftedQupComponents.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ZerothHomotopy (QuillenUniverseLift.canonicalLoops.{uR, uM} R) →
    ZerothHomotopy (QuillenUniverseLift.originalLoops.{uR, uM, uObj, uHom} R) :=
  actualLoopComponentsMap (originalUnliftedQup.{uR, uM, uObj, uHom, uNative} R)

/-- Both actual component directions are inverse on EVERY original component. -/
public theorem originalUnliftedQcomponent_inverse_laws.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] :
    (∀ c, originalUnliftedQupComponents.{uR, uM, uObj, uHom, uNative} R
      (originalUnliftedQdownComponents.{uR, uM, uObj, uHom, uNative} R c) = c) ∧
    (∀ c, originalUnliftedQdownComponents.{uR, uM, uObj, uHom, uNative} R
      (originalUnliftedQupComponents.{uR, uM, uObj, uHom, uNative} R c) = c) := by
  constructor
  · intro c
    induction c using ZerothHomotopy.rec with
    | mk p =>
        exact ZerothHomotopy.sound
          ((originalUnliftedQleftFamily.{uR, uM, uObj, uHom, uNative} R).toHomotopy.evalAt p)
  · intro c
    induction c using ZerothHomotopy.rec with
    | mk p =>
        exact ZerothHomotopy.sound
          ((originalUnliftedQrightFamily.{uR, uM, uObj, uHom, uNative} R).toHomotopy.evalAt p)

private def originalQdownK0Action.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] : K0 (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R) →+
    K0 (QuillenUniverseLift.canonicalCategory.{uR, uM} R) :=
  (originalQFundamentalK0Equiv (QuillenUniverseLift.canonicalCategory.{uR, uM}
    R)).toAddMonoidHom.comp
    ((basedFundamentalGroupMap (QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R).hom
      (QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R).rootPath).toAdditive.comp
      (originalQFundamentalK0Equiv (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom}
        R)).symm.toAddMonoidHom)

private theorem originalQdownK0Action_generator.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] (X : QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R) :
    originalQdownK0Action.{uR, uM, uObj, uHom} R (K0.mk X) =
      K0.mk ((FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj X) := by
  let A := originalQFundamentalK0Equiv (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
  let B := originalQFundamentalK0Equiv (QuillenUniverseLift.canonicalCategory.{uR, uM} R)
  let f := QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R
  let p := OriginalQK0Comparison.generatorLoop X
  let g := Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
  have hGenerator : A g = K0.mk X :=
    (originalQFundamentalK0Equiv_loop _ p).trans
      (OriginalQK0Comparison.generatorLoop_canonical X)
  have hInverse : A.symm (K0.mk X) = g :=
    A.injective ((A.apply_symm_apply (K0.mk X)).trans hGenerator.symm)
  change B ((basedFundamentalGroupMap f.hom f.rootPath).toAdditive (A.symm (K0.mk X))) = _
  rw [hInverse]
  have hMap := basedFundamentalGroupMap_mk f.hom f.rootPath p
  have hLoop := originalQFundamentalK0Equiv_loop _ (f.loopMap p)
  have hComponent := zerothHomotopy_mk_eq_of_pathHomotopic
    (QuillenUniverseLift.qDownWeaklyPointed_generator R X)
  exact (congrArg (fun g => B (Additive.ofMul g)) hMap).trans
    (hLoop.trans ((congrArg (OriginalQK0Comparison.canonicalLoopComponentsK0
      (C := QuillenUniverseLift.canonicalCategory.{uR, uM} R)) hComponent).trans
        (OriginalQK0Comparison.generatorLoop_canonical _)))

private theorem originalQdownK0Action_eq_map.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] : originalQdownK0Action.{uR, uM, uObj, uHom} R =
    K0.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R) := by
  apply K0.hom_ext
  intro X
  exact (originalQdownK0Action_generator R X).trans (K0.map_mk _ X).symm

private theorem originalQdownWeakEvaluator.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] (p : QuillenUniverseLift.originalLoops.{uR, uM, uObj, uHom} R) :
    OriginalQK0Comparison.canonicalLoopComponentsK0
        (C := QuillenUniverseLift.canonicalCategory.{uR, uM} R)
        (ZerothHomotopy.mk ((QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap
          p)) =
      K0.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)
        (OriginalQK0Comparison.canonicalLoopComponentsK0
          (C := QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R) (ZerothHomotopy.mk p))
            := by
  let A := originalQFundamentalK0Equiv (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
  let B := originalQFundamentalK0Equiv (QuillenUniverseLift.canonicalCategory.{uR, uM} R)
  let f := QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R
  let g := Additive.ofMul (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
  have hMap := basedFundamentalGroupMap_mk f.hom f.rootPath p
  have hSource := originalQFundamentalK0Equiv_loop _ p
  have hTarget := originalQFundamentalK0Equiv_loop _ (f.loopMap p)
  have hAction := congrArg (fun k => k (A g)) (originalQdownK0Action_eq_map R)
  have hInverse := A.symm_apply_apply g
  have hActual : B ((basedFundamentalGroupMap f.hom f.rootPath).toAdditive g) =
      originalQdownK0Action.{uR, uM, uObj, uHom} R (A g) :=
    (congrArg (fun p => B ((basedFundamentalGroupMap f.hom f.rootPath).toAdditive p)) hInverse).symm
  exact hTarget.symm.trans ((congrArg (fun p => B (Additive.ofMul p)) hMap.symm).trans
    (hActual.trans (hAction.trans (congrArg (K0.map
      (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)) hSource))))

/-- The evaluator of EVERY actual unlifted component is the original K0.map
    of the canonical category descent, not a redefined evaluator. -/
public theorem originalUnliftedQdownEvaluator.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] (c : ZerothHomotopy
      (QuillenUniverseLift.originalLoops.{uR, uM, uObj, uHom} R)) :
    OriginalQK0Comparison.canonicalLoopComponentsK0
        (C := QuillenUniverseLift.canonicalCategory.{uR, uM} R)
        (originalUnliftedQdownComponents.{uR, uM, uObj, uHom, uNative} R c) =
      K0.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)
        (OriginalQK0Comparison.canonicalLoopComponentsK0
          (C := QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R) c) := by
  induction c using ZerothHomotopy.rec with
  | mk p =>
      let up := QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R
      let down := QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R
      have hComponents := QuillenUniverseLift.Qdown_components.{uR, uM, uObj, uHom, uNative} R (up
        p)
      have hCarrier : down (up p) = p := congrArg (fun f => f p)
        (QuillenUniverseLift.rawNativeCarrierDown_comp_up.{uR, uM, uObj, uHom, uNative} R)
      have hOriginal : ZerothHomotopy.mk (originalUnliftedQdown.{uR, uM, uObj, uHom, uNative} R p) =
          ZerothHomotopy.mk ((QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap
            p) :=
        hComponents.trans (congrArg (fun p => ZerothHomotopy.mk
          ((QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap p)) hCarrier)
      exact (congrArg (OriginalQK0Comparison.canonicalLoopComponentsK0
        (C := QuillenUniverseLift.canonicalCategory.{uR, uM} R)) hOriginal).trans
        (originalQdownWeakEvaluator R p)

private theorem originalK0DownInjective.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] : Function.Injective
    (K0.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)) := by
  let E := FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R
  let _ : E.functor.Additive := FGProjectiveCat.CategoryUniverseLift.upFunctorAdditive R
  let _ : E.inverse.Additive := FGProjectiveCat.CategoryUniverseLift.downFunctorAdditive R
  let _ : E.functor.IsExact := FGProjectiveCat.CategoryUniverseLift.upFunctorIsExact R
  let _ : E.inverse.IsExact := FGProjectiveCat.CategoryUniverseLift.downFunctorIsExact R
  exact (K0.equivOfEquivalence E).symm.injective

private theorem originalK0DownUp.{uR, uM, uObj, uHom}
    (R : Type uR) [Ring R] (x : K0 (QuillenUniverseLift.canonicalCategory.{uR, uM} R)) :
    K0.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)
        (K0.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R) x) = x := by
  let E := FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R
  let _ : E.functor.Additive := FGProjectiveCat.CategoryUniverseLift.upFunctorAdditive R
  let _ : E.inverse.Additive := FGProjectiveCat.CategoryUniverseLift.downFunctorAdditive R
  let _ : E.functor.IsExact := FGProjectiveCat.CategoryUniverseLift.upFunctorIsExact R
  let _ : E.inverse.IsExact := FGProjectiveCat.CategoryUniverseLift.downFunctorIsExact R
  exact (K0.equivOfEquivalence E).symm_apply_apply x

/-- The other actual unlifted evaluator direction retains EVERY component,
    using the SAME original full inverse family and actual category lift. -/
public theorem originalUnliftedQupEvaluator.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] (c : ZerothHomotopy (QuillenUniverseLift.canonicalLoops.{uR, uM} R)) :
    OriginalQK0Comparison.canonicalLoopComponentsK0
        (C := QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
        (originalUnliftedQupComponents.{uR, uM, uObj, uHom, uNative} R c) =
      K0.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R)
        (OriginalQK0Comparison.canonicalLoopComponentsK0
          (C := QuillenUniverseLift.canonicalCategory.{uR, uM} R) c) := by
  apply originalK0DownInjective R
  have hDown := originalUnliftedQdownEvaluator.{uR, uM, uObj, uHom, uNative} R
    (originalUnliftedQupComponents.{uR, uM, uObj, uHom, uNative} R c)
  have hInverse := (originalUnliftedQcomponent_inverse_laws.{uR, uM, uObj, uHom, uNative} R).2 c
  exact hDown.symm.trans
    ((congrArg (OriginalQK0Comparison.canonicalLoopComponentsK0
      (C := QuillenUniverseLift.canonicalCategory.{uR, uM} R)) hInverse).trans
        (originalK0DownUp R _).symm)


private def originalLoopPointHomeomorph.{uX}
    {X : Type uX} [TopologicalSpace X] {x y : X} (h : x = y) :
    LoopSpace X x ≃ₜ LoopSpace X y := by
  cases h
  exact Homeomorph.refl _

private theorem originalLoopPointHomeomorph_value.{uX}
    {X : Type uX} [TopologicalSpace X] {x y : X} (h : x = y) (p : LoopSpace X x)
    (t : unitInterval) : originalLoopPointHomeomorph h p t = p t := by
  cases h
  rfl

/-- The original NQ basepoint equality changes ONLY loop endpoints, preserving
    every original loop value at every interval time. -/
public def originalNQLoopPointHomeomorph.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] : NQKSpace C ≃ₜ BasedSplitExactQLoop.originalQLoops
      (C := C) :=
  originalLoopPointHomeomorph (NQReal.basepoint_eq_realizedVertex C)

/-- The existing original Q0 evaluator has exactly the same value after its
    prescribed basepoint-to-zero-vertex equality cast. -/
public theorem originalNQLoopPointEvaluator.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (p : NQKSpace C) :
    OriginalQK0Comparison.canonicalLoopComponentsK0 (C := C)
        (ZerothHomotopy.mk (originalNQLoopPointHomeomorph C p)) =
      WaldhausenKTheory.K0.toExact C (NQKSpacePiZeroEquivK0 C (ZerothHomotopy.mk p)) := by
  let q := originalNQLoopPointHomeomorph C p
  have hCast : q.cast (NQReal.basepoint_eq_realizedVertex C)
      (NQReal.basepoint_eq_realizedVertex C) = p := by
    apply Path.ext
    funext t
    exact originalLoopPointHomeomorph_value (NQReal.basepoint_eq_realizedVertex C) p t
  exact (OriginalQK0Comparison.canonicalLoopComponentsK0_mk (C := C) q).trans
    (congrArg (fun c => WaldhausenKTheory.K0.toExact C (NQKSpacePiZeroEquivK0 C c))
      (congrArg ZerothHomotopy.mk hCast))

private theorem originalNQLoopPointHomeomorph_constant.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] : originalNQLoopPointHomeomorph C (Path.refl
      (NQReal.basepoint C)) =
    BasedSplitExactQLoop.constantQLoop (C := C) := by
  apply Path.ext
  funext t
  exact (originalLoopPointHomeomorph_value (NQReal.basepoint_eq_realizedVertex C)
    (Path.refl (NQReal.basepoint C)) t).trans (NQReal.basepoint_eq_realizedVertex C)

/-- The original unlifted Qdown on the original stock NQKSpace carriers. -/
public def originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : C(NQKSpace (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R),
    NQKSpace (QuillenUniverseLift.canonicalCategory.{uR, uM} R)) :=
  (originalNQLoopPointHomeomorph (QuillenUniverseLift.canonicalCategory.{uR, uM}
    R)).symm.toHomotopyEquiv.toFun.comp
    ((originalUnliftedQdown.{uR, uM, uObj, uHom, uNative} R).comp
      (originalNQLoopPointHomeomorph (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom}
        R)).toHomotopyEquiv.toFun)

/-- Its actual original inverse on the SAME original NQ loop carriers. -/
public def originalUnliftedNQup.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : C(NQKSpace (QuillenUniverseLift.canonicalCategory.{uR, uM} R),
    NQKSpace (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)) :=
  (originalNQLoopPointHomeomorph (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom}
    R)).symm.toHomotopyEquiv.toFun.comp
    ((originalUnliftedQup.{uR, uM, uObj, uHom, uNative} R).comp
      (originalNQLoopPointHomeomorph (QuillenUniverseLift.canonicalCategory.{uR, uM}
        R)).toHomotopyEquiv.toFun)

/-- BOTH full original inverse families remain relative to the original NQ constants. -/
public def originalUnliftedNQleftFamily.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ContinuousMap.HomotopyRel
    ((originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R).comp (originalUnliftedNQdown.{uR, uM,
      uObj, uHom, uNative} R))
    (ContinuousMap.id (NQKSpace (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)))
    {Path.refl (NQReal.basepoint (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R))} := by
  let A := originalNQLoopPointHomeomorph (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
  let B := originalNQLoopPointHomeomorph (QuillenUniverseLift.canonicalCategory.{uR, uM} R)
  let x := Path.refl (NQReal.basepoint (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R))
  let H := ((originalUnliftedQleftFamily.{uR, uM, uObj, uHom, uNative} R).precomposePointRelative
    A.toHomotopyEquiv.toFun x (originalNQLoopPointHomeomorph_constant _)).compContinuousMap
      A.symm.toHomotopyEquiv.toFun
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro p
    exact (congrArg (fun q => A.symm (originalUnliftedQup.{uR, uM, uObj, uHom, uNative} R q))
      (B.apply_symm_apply (originalUnliftedQdown.{uR, uM, uObj, uHom, uNative} R (A p)))).symm
  · apply ContinuousMap.ext
    intro p
    exact A.symm_apply_apply p

/-- The entire other original inverse family retains the original target NQ constant. -/
public def originalUnliftedNQrightFamily.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ContinuousMap.HomotopyRel
    ((originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R).comp (originalUnliftedNQup.{uR, uM,
      uObj, uHom, uNative} R))
    (ContinuousMap.id (NQKSpace (QuillenUniverseLift.canonicalCategory.{uR, uM} R)))
    {Path.refl (NQReal.basepoint (QuillenUniverseLift.canonicalCategory.{uR, uM} R))} := by
  let A := originalNQLoopPointHomeomorph (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
  let B := originalNQLoopPointHomeomorph (QuillenUniverseLift.canonicalCategory.{uR, uM} R)
  let x := Path.refl (NQReal.basepoint (QuillenUniverseLift.canonicalCategory.{uR, uM} R))
  let H := ((originalUnliftedQrightFamily.{uR, uM, uObj, uHom, uNative} R).precomposePointRelative
    B.toHomotopyEquiv.toFun x (originalNQLoopPointHomeomorph_constant _)).compContinuousMap
      B.symm.toHomotopyEquiv.toFun
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro p
    exact (congrArg (fun q => B.symm (originalUnliftedQdown.{uR, uM, uObj, uHom, uNative} R q))
      (A.apply_symm_apply (originalUnliftedQup.{uR, uM, uObj, uHom, uNative} R (B p)))).symm
  · apply ContinuousMap.ext
    intro p
    exact B.symm_apply_apply p

/-- Every time of BOTH original transported inverse families fixes its NQ root. -/
public theorem originalUnliftedNQfamily_roots.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] (t : unitInterval) :
    originalUnliftedNQleftFamily.{uR, uM, uObj, uHom, uNative} R
      (t, Path.refl (NQReal.basepoint (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom}
        R))) =
        Path.refl (NQReal.basepoint (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)) ∧
    originalUnliftedNQrightFamily.{uR, uM, uObj, uHom, uNative} R
      (t, Path.refl (NQReal.basepoint (QuillenUniverseLift.canonicalCategory.{uR, uM} R))) =
        Path.refl (NQReal.basepoint (QuillenUniverseLift.canonicalCategory.{uR, uM} R)) :=
  ⟨(originalUnliftedNQleftFamily.{uR, uM, uObj, uHom, uNative} R).eq_snd t (by rfl),
    (originalUnliftedNQrightFamily.{uR, uM, uObj, uHom, uNative} R).eq_snd t (by rfl)⟩

/-- The SAME original NQ descent induces its component map on the stock loop carrier. -/
public def originalUnliftedNQdownComponents.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ZerothHomotopy (NQKSpace
      (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)) →
    ZerothHomotopy (NQKSpace (QuillenUniverseLift.canonicalCategory.{uR, uM} R)) :=
  actualLoopComponentsMap (originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R)

/-- The SAME original NQ inclusion induces the inverse component map on the stock carrier. -/
public def originalUnliftedNQupComponents.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : ZerothHomotopy (NQKSpace
      (QuillenUniverseLift.canonicalCategory.{uR, uM} R)) →
    ZerothHomotopy (NQKSpace (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)) :=
  actualLoopComponentsMap (originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R)

/-- The evaluator of EVERY original NQ component transports by actual category descent. -/
public theorem originalUnliftedNQdownEvaluator.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] (c : ZerothHomotopy (NQKSpace
      (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R))) :
    WaldhausenKTheory.K0.toExact (QuillenUniverseLift.canonicalCategory.{uR, uM} R)
        (NQKSpacePiZeroEquivK0 (QuillenUniverseLift.canonicalCategory.{uR, uM} R)
          (originalUnliftedNQdownComponents.{uR, uM, uObj, uHom, uNative} R c)) =
      K0.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)
        (WaldhausenKTheory.K0.toExact (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
          (NQKSpacePiZeroEquivK0 (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R) c))
            := by
  induction c using ZerothHomotopy.rec with
  | mk p =>
      let A := originalNQLoopPointHomeomorph (QuillenUniverseLift.liftedCategory.{uR, uM, uObj,
        uHom}
        R)
      let B := originalNQLoopPointHomeomorph (QuillenUniverseLift.canonicalCategory.{uR, uM} R)
      have hMap : B (originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R p) =
        originalUnliftedQdown.{uR, uM, uObj, uHom, uNative} R (A p) :=
        B.apply_symm_apply _
      have hOriginal := originalUnliftedQdownEvaluator.{uR, uM, uObj, uHom, uNative} R
        (ZerothHomotopy.mk (A p))
      exact (originalNQLoopPointEvaluator _ (originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative}
        R p)).symm.trans
        ((congrArg (fun p => OriginalQK0Comparison.canonicalLoopComponentsK0
          (C := QuillenUniverseLift.canonicalCategory.{uR, uM} R) (ZerothHomotopy.mk p)) hMap).trans
          (hOriginal.trans (congrArg (K0.map
            (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R))
              (originalNQLoopPointEvaluator _ p))))

/-- The evaluator in the other direction retains EVERY original NQ component. -/
public theorem originalUnliftedNQupEvaluator.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] (c : ZerothHomotopy (NQKSpace
      (QuillenUniverseLift.canonicalCategory.{uR, uM} R))) :
    WaldhausenKTheory.K0.toExact (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
        (NQKSpacePiZeroEquivK0 (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)
          (originalUnliftedNQupComponents.{uR, uM, uObj, uHom, uNative} R c)) =
      K0.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R)
        (WaldhausenKTheory.K0.toExact (QuillenUniverseLift.canonicalCategory.{uR, uM} R)
          (NQKSpacePiZeroEquivK0 (QuillenUniverseLift.canonicalCategory.{uR, uM} R) c)) := by
  induction c using ZerothHomotopy.rec with
  | mk p =>
      let A := originalNQLoopPointHomeomorph (QuillenUniverseLift.liftedCategory.{uR, uM, uObj,
        uHom}
        R)
      let B := originalNQLoopPointHomeomorph (QuillenUniverseLift.canonicalCategory.{uR, uM} R)
      have hMap : A (originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R p) =
        originalUnliftedQup.{uR, uM, uObj, uHom, uNative} R (B p) :=
        A.apply_symm_apply _
      have hOriginal := originalUnliftedQupEvaluator.{uR, uM, uObj, uHom, uNative} R
        (ZerothHomotopy.mk (B p))
      exact (originalNQLoopPointEvaluator _ (originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R
        p)).symm.trans
        ((congrArg (fun p => OriginalQK0Comparison.canonicalLoopComponentsK0
          (C := QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R) (ZerothHomotopy.mk p))
            hMap).trans
          (hOriginal.trans (congrArg (K0.map
            (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R))
              (originalNQLoopPointEvaluator _ p))))

end AlgebraicKTheory.OriginalQuillenUnliftedTransport

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.OriginalQuillenUnliftedTransport

private theorem originalNQLoopPointHomeomorphValueComputed.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (p : NQKSpace C) (t : unitInterval) :
    originalNQLoopPointHomeomorph C p t = p t :=
  originalLoopPointHomeomorph_value (NQReal.basepoint_eq_realizedVertex C) p t

/-- Every original loop time has its literal value under the SAME point homeomorphism. -/
public theorem originalNQLoopPointHomeomorph_value.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (p : NQKSpace C) (t : unitInterval) :
    originalNQLoopPointHomeomorph C p t = p t :=
  originalNQLoopPointHomeomorphValueComputed C p t

private theorem originalNQLoopPointHomeomorphSymmValueComputed.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C]
    (p : BasedSplitExactQLoop.originalQLoops (C := C)) (t : unitInterval) :
    (originalNQLoopPointHomeomorph C).symm p t = p t := by
  let e := originalNQLoopPointHomeomorph C
  have hForward := originalNQLoopPointHomeomorph_value C (e.symm p) t
  have hInverse := congrArg
    (fun q : BasedSplitExactQLoop.originalQLoops (C := C) => q t) (e.apply_symm_apply p)
  exact hForward.symm.trans hInverse

/-- The actual inverse of that SAME homeomorphism retains every original loop time. -/
public theorem originalNQLoopPointHomeomorph_symm_value.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C]
    (p : BasedSplitExactQLoop.originalQLoops (C := C)) (t : unitInterval) :
    (originalNQLoopPointHomeomorph C).symm p t = p t :=
  originalNQLoopPointHomeomorphSymmValueComputed C p t

end AlgebraicKTheory.OriginalQuillenUnliftedTransport

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.OriginalQuillenUnliftedTransport

private theorem originalUnliftedNQdownValueComputed.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R =
    (originalNQLoopPointHomeomorph
      (QuillenUniverseLift.canonicalCategory.{uR, uM} R)).symm.toHomotopyEquiv.toFun.comp
      (((QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R).comp
        (QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R)).comp
        (originalNQLoopPointHomeomorph
      (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)).toHomotopyEquiv.toFun) := by
  rfl

/-- The whole original unlifted NQ down map retains its SAME charts and native carrier recipe. -/
public theorem originalUnliftedNQdown_value.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R =
    (originalNQLoopPointHomeomorph
      (QuillenUniverseLift.canonicalCategory.{uR, uM} R)).symm.toHomotopyEquiv.toFun.comp
      (((QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R).comp
        (QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R)).comp
        (originalNQLoopPointHomeomorph
      (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)).toHomotopyEquiv.toFun) :=
  originalUnliftedNQdownValueComputed R

private theorem originalUnliftedNQupValueComputed.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R =
    (originalNQLoopPointHomeomorph
      (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)).symm.toHomotopyEquiv.toFun.comp
      (((QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
        (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R)).comp
        (originalNQLoopPointHomeomorph
      (QuillenUniverseLift.canonicalCategory.{uR, uM} R)).toHomotopyEquiv.toFun) := by
  rfl

/-- The whole original unlifted NQ up map retains its SAME charts and native carrier recipe. -/
public theorem originalUnliftedNQup_value.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R =
    (originalNQLoopPointHomeomorph
      (QuillenUniverseLift.liftedCategory.{uR, uM, uObj, uHom} R)).symm.toHomotopyEquiv.toFun.comp
      (((QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R).comp
        (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R)).comp
        (originalNQLoopPointHomeomorph
      (QuillenUniverseLift.canonicalCategory.{uR, uM} R)).toHomotopyEquiv.toFun) :=
  originalUnliftedNQupValueComputed R

end AlgebraicKTheory.OriginalQuillenUnliftedTransport

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.OriginalQuillenUnliftedTransport

private theorem originalUnliftedNQupComponentsValueComputed.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : originalUnliftedNQupComponents.{uR, uM, uObj, uHom, uNative} R =
      ZerothHomotopy.lift
        (fun p => ZerothHomotopy.mk (originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R p))
        (fun {_ _} path => ZerothHomotopy.sound
          (path.map (originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R).continuous)) := by
  rfl

/-- The WHOLE original up component map is the actual quotient map of its SAME continuous up map. -/
public theorem originalUnliftedNQupComponents_value.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : originalUnliftedNQupComponents.{uR, uM, uObj, uHom, uNative} R =
      ZerothHomotopy.lift
        (fun p => ZerothHomotopy.mk (originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R p))
        (fun {_ _} path => ZerothHomotopy.sound
          (path.map (originalUnliftedNQup.{uR, uM, uObj, uHom, uNative} R).continuous)) :=
  originalUnliftedNQupComponentsValueComputed R

end AlgebraicKTheory.OriginalQuillenUnliftedTransport

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.OriginalQuillenUnliftedTransport

private theorem originalUnliftedNQdownComponentsValueComputed.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : originalUnliftedNQdownComponents.{uR, uM, uObj, uHom, uNative} R =
      ZerothHomotopy.lift
        (fun p => ZerothHomotopy.mk (originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R p))
        (fun {_ _} path => ZerothHomotopy.sound
          (path.map (originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R).continuous)) := by
  rfl

/-- The WHOLE original down component map is the actual quotient map of its SAME down map. -/
public theorem originalUnliftedNQdownComponents_value.{uR, uM, uObj, uHom, uNative}
    (R : Type uR) [Ring R] : originalUnliftedNQdownComponents.{uR, uM, uObj, uHom, uNative} R =
      ZerothHomotopy.lift
        (fun p => ZerothHomotopy.mk (originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R p))
        (fun {_ _} path => ZerothHomotopy.sound
          (path.map (originalUnliftedNQdown.{uR, uM, uObj, uHom, uNative} R).continuous)) :=
  originalUnliftedNQdownComponentsValueComputed R

end AlgebraicKTheory.OriginalQuillenUnliftedTransport

end

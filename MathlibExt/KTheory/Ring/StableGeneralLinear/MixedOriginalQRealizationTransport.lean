/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.MixedOriginalQUniverseRootTransport
public import MathlibExt.KTheory.Exact.Quillen.NQKSpaceContinuousMap
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagGroupNaturality
public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap

/-!
# Actual mixed original Q realization, root and loop transport

The original mixed realization adapter maps QuillenQ.map F on the original
NQReal carriers. Its canonical mapped-zero Iso supplies the actual root path.
The generic weakly pointed loop construction retains the original conjugation
clock. Same-frame values recover the original NQReal/root/K-space/pi0/evaluator
APIs. The accepted categorical up/down lifts are actual specializations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial ZeroObject

attribute [local instance] CategoryTheory.uliftCategory

namespace AlgebraicKTheory.QuillenMixedUniverseTransport

/-- Actual QuillenQ.map realization between original independent category worlds. -/
public def mixedNQRealMap.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : C(NQReal C, NQReal D) :=
  CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F)

/-- The entire selected map has its original mixed nerve-functor value. -/
public theorem mixedNQRealMap_value.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : mixedNQRealMap F =
      CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F) := by
  rfl

/-- The original source zero vertex maps to its actual Q-functor image vertex. -/
public theorem mixedNQRealMap_zeroVertex.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : mixedNQRealMap F (NQReal.basepoint C) =
    SSet.realizedVertex (X := NQ D)
      (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))) := by
  let M := CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F)
  have hValue := congrArg (fun f : C(NQReal C, NQReal D) => f (NQReal.basepoint C))
    (mixedNQRealMap_value F)
  exact hValue.trans ((congrArg M (NQReal.basepoint_eq_realizedVertex C)).trans
    (CategoryTheory.realizedNerveFunctorMap_vertex (QuillenQ.map F) (⟨0⟩ : QuillenQ C)))

/-- The SAME canonical Q.zeroComparisonIso gives the mapped-to-target root;
    the original selected zeros are retained without a strict-point assertion. -/
public def mixedNQRootPath.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : Path (mixedNQRealMap F (NQReal.basepoint C))
      (NQReal.basepoint D) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (QuillenQ.zeroComparisonIso F).hom))).cast
      (mixedNQRealMap_zeroVertex F) (NQReal.basepoint_eq_realizedVertex D)

/-- Every original interval time keeps the actual canonical comparison edge value. -/
public theorem mixedNQRootPath_value.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] (t : unitInterval) : mixedNQRootPath F t =
    TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (QuillenQ.zeroComparisonIso F).hom)) t := by
  rfl

/-- The actual original Q realization map with that SAME canonical weak root. -/
public def mixedNQWeaklyPointedMap.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : ContinuousMap.WeaklyPointed (NQReal.basepoint C)
      (NQReal.basepoint D) where
  hom := mixedNQRealMap F
  rootPath := mixedNQRootPath F

/-- The induced continuous loop map uses the original one-fold NQKSpace carrier. -/
public def mixedNQKSpaceMap.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : C(NQKSpace C, NQKSpace D) :=
  (mixedNQWeaklyPointedMap F).loopMap

/-- The whole loop value retains the actual canonical root and conjugation clock. -/
public theorem mixedNQKSpaceMap_value.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] (gamma : NQKSpace C) : mixedNQKSpaceMap F gamma =
    (mixedNQRootPath F).symm.trans
      ((gamma.map (mixedNQRealMap F).continuous).trans (mixedNQRootPath F)) :=
  ContinuousMap.WeaklyPointed.loopMap_apply (mixedNQWeaklyPointedMap F) gamma

/-- The actual path-component map of that same canonical weakly pointed Q map. -/
public def mixedNQKSpacePiZeroMap.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : ZerothHomotopy (NQKSpace C) → ZerothHomotopy (NQKSpace
      D) :=
  (mixedNQWeaklyPointedMap F).loopComponentsMap

/-- Every loop representative maps through the same actual continuous loop map. -/
public theorem mixedNQKSpacePiZeroMap_mk.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] (gamma : NQKSpace C) :
    mixedNQKSpacePiZeroMap F (ZerothHomotopy.mk gamma) =
      ZerothHomotopy.mk (mixedNQKSpaceMap F gamma) :=
  ContinuousMap.WeaklyPointed.loopComponentsMap_mk (mixedNQWeaklyPointedMap F) gamma

/-- Calibration at a genuinely shared original frame recovers original NQReal.map. -/
public theorem mixedNQRealMap_sameFrame.{u, v}
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : mixedNQRealMap F = (NQReal.map F).hom :=
  (mixedNQRealMap_value F).trans
    (CategoryTheory.realizedNerveFunctorMap_sameFrame (QuillenQ.map F))

/-- The full SAME-frame root is the original prescribed root path with only
    its actual source-map equality transport. -/
public theorem mixedNQRootPath_sameFrame.{u, v}
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : mixedNQRootPath F =
    (NQKSpace.zeroComparisonRootPath C D F).cast
      (congrArg (fun f : C(NQReal C, NQReal D) => f (NQReal.basepoint C))
        (mixedNQRealMap_sameFrame F)) rfl := by
  let a := nerve.edgeMk (QuillenQ.zeroComparisonIso F).hom
  let b := NQ.zeroComparisonEdge F
  have hEdge : a.edge = b.edge := (NQ.zeroComparisonEdge_edge F).symm
  have hHom : (SSet.realizedEdgePath a).hom = (SSet.realizedEdgePath b).hom :=
    (SSet.realizedEdgePath_hom a).trans
      ((congrArg (fun z : (NQ D) _⦋1⦌ =>
        SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map (SSet.yonedaEquiv.symm z)) hEdge).trans
          (SSet.realizedEdgePath_hom b).symm)
  apply Path.ext
  funext t
  exact (mixedNQRootPath_value F t).trans
    (ConcreteCategory.congr_hom hHom (TopCat.I.homeomorph.{max u v}.symm t))

private theorem originalConjugateLoopMapCastValue.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : C(X, Y)) (h : f = g)
    (p : Path (f x) y) (q : Path (g x) y)
    (hp : p = q.cast (congrArg (fun a : C(X, Y) => a x) h) rfl)
    (gamma : LoopSpace X x) :
    p.symm.trans ((gamma.map f.continuous).trans p) =
      q.symm.trans ((gamma.map g.continuous).trans q) := by
  cases h
  cases hp
  rfl

/-- SAME-frame loop values are the actual original NQKSpaceContinuousMap. -/
public theorem mixedNQKSpaceMap_sameFrame.{u, v}
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : mixedNQKSpaceMap F = NQKSpaceContinuousMap F := by
  apply ContinuousMap.ext
  intro gamma
  have h := originalConjugateLoopMapCastValue (mixedNQRealMap F) (NQReal.map F).hom
    (mixedNQRealMap_sameFrame F) (mixedNQRootPath F)
    (NQKSpace.zeroComparisonRootPath C D F) (mixedNQRootPath_sameFrame F) gamma
  have hOriginal := (NQKSpaceContinuousMap_apply F gamma).trans
    (NQKSpaceMap_apply C D F gamma)
  exact (mixedNQKSpaceMap_value F gamma).trans (h.trans hOriginal.symm)

/-- SAME-frame component values recover the actual original Q/S component map. -/
public theorem mixedNQKSpacePiZeroMap_sameFrame.{u, v}
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] : mixedNQKSpacePiZeroMap F = NQKSpacePiZeroMap F := by
  funext c
  induction c using ZerothHomotopy.rec with
  | mk gamma =>
      have hMap := mixedNQKSpacePiZeroMap_mk F gamma
      have hOriginal := ContinuousMap.WeaklyPointed.loopComponentsMap_mk
        (NQRealMapWeaklyPointed F) gamma
      exact hMap.trans ((congrArg ZerothHomotopy.mk
        (congrArg (fun f : C(NQKSpace C, NQKSpace D) => f gamma)
          (mixedNQKSpaceMap_sameFrame F))).trans hOriginal.symm)

section OriginalExactWaldhausenEvaluator

attribute [local instance] CategoryTheory.ExactCategory.waldhausenCategory

private theorem originalQComponentMapAtSameFrame.{u, v}
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] (c : ZerothHomotopy (NQKSpace C)) :
    mixedNQKSpacePiZeroMap F c = NQKSpacePiZeroMap F c :=
  congrArg
    (fun f : ZerothHomotopy (NQKSpace C) → ZerothHomotopy (NQKSpace D) => f c)
    (mixedNQKSpacePiZeroMap_sameFrame F)

private theorem originalQEvaluatorValueAtSameFrame.{u, v}
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] (c : ZerothHomotopy (NQKSpace C)) :
    NQKSpacePiZeroEquivK0 D (mixedNQKSpacePiZeroMap F c) =
      NQKSpacePiZeroEquivK0 D (NQKSpacePiZeroMap F c) := by
  let E : ZerothHomotopy (NQKSpace D) →
      @WaldhausenKTheory.K0 D _ _ (CategoryTheory.ExactCategory.waldhausenCategory D) :=
    NQKSpacePiZeroEquivK0 D
  exact congrArg E (originalQComponentMapAtSameFrame F c)

/-- The SAME-frame original Q0 evaluator obeys its original exact-functor law
    for the actual calibrated mixed map, on EVERY loop component. -/
public theorem mixedNQKSpacePiZeroEvaluator_sameFrame.{u, v}
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] (c : ZerothHomotopy (NQKSpace C)) :
    NQKSpacePiZeroEquivK0 D (mixedNQKSpacePiZeroMap F c) =
      WaldhausenKTheory.K0.map F (NQKSpacePiZeroEquivK0 C c) :=
  by
    let X := ZerothHomotopy (NQKSpace C)
    let Y := ZerothHomotopy (NQKSpace D)
    let A : X →
        @WaldhausenKTheory.K0 C _ _ (CategoryTheory.ExactCategory.waldhausenCategory C) :=
      NQKSpacePiZeroEquivK0 C
    let B : Y →
        @WaldhausenKTheory.K0 D _ _ (CategoryTheory.ExactCategory.waldhausenCategory D) :=
      NQKSpacePiZeroEquivK0 D
    let m : X → Y := mixedNQKSpacePiZeroMap F
    let n : X → Y := NQKSpacePiZeroMap F
    have hValue : B (m c) = B (n c) := originalQEvaluatorValueAtSameFrame F c
    have hOriginal : B (n c) = WaldhausenKTheory.K0.map F (A c) :=
      NQKSpacePiZeroEquivK0_naturality F c
    exact hValue.trans hOriginal

end OriginalExactWaldhausenEvaluator

end AlgebraicKTheory.QuillenMixedUniverseTransport

namespace AlgebraicKTheory.StableGL

/-- The original R up-functor with its actual canonical Q zero root. -/
public def mixedOriginalQUpWeakMapR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :
    ContinuousMap.WeaklyPointed (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R))
      (NQReal.basepoint (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R)) :=
  QuillenMixedUniverseTransport.mixedNQWeaklyPointedMap
    (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR, max (max uR uMR + 1) (max uS uMS +
    1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R)

/-- The SAME actual R up-functor on original one-fold Q loop carriers. -/
public def mixedOriginalQUpLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :
    C(NQKSpace (FGProjectiveCat.{max uR uMR} R), NQKSpace (mixedOriginalQWorkingCategoryR.{uR, uS,
      uMR, uMS, uNR, uNS} R)) :=
  (mixedOriginalQUpWeakMapR.{uR, uS, uMR, uMS, uNR, uNS} R).loopMap

/-- The original S up-functor with its actual canonical Q zero root. -/
public def mixedOriginalQUpWeakMapS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :
    ContinuousMap.WeaklyPointed (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))
      (NQReal.basepoint (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S)) :=
  QuillenMixedUniverseTransport.mixedNQWeaklyPointedMap
    (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS, max (max uR uMR + 1) (max uS uMS +
    1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S)

/-- The SAME actual S up-functor on original one-fold Q loop carriers. -/
public def mixedOriginalQUpLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :
    C(NQKSpace (FGProjectiveCat.{max uS uMS} S), NQKSpace (mixedOriginalQWorkingCategoryS.{uR, uS,
      uMR, uMS, uNR, uNS} S)) :=
  (mixedOriginalQUpWeakMapS.{uR, uS, uMR, uMS, uNR, uNS} S).loopMap

/-- The original R down-functor with its actual canonical Q zero root. -/
public def mixedOriginalQDownWeakMapR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :
    ContinuousMap.WeaklyPointed (NQReal.basepoint (mixedOriginalQWorkingCategoryR.{uR, uS, uMR,
      uMS, uNR, uNS} R)) (NQReal.basepoint (FGProjectiveCat.{max uR uMR} R)) :=
  QuillenMixedUniverseTransport.mixedNQWeaklyPointedMap
    (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uMR, max (max uR uMR + 1) (max uS uMS +
    1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} R)

/-- The SAME actual R down-functor on original one-fold Q loop carriers. -/
public def mixedOriginalQDownLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :
    C(NQKSpace (mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R), NQKSpace
      (FGProjectiveCat.{max uR uMR} R)) :=
  (mixedOriginalQDownWeakMapR.{uR, uS, uMR, uMS, uNR, uNS} R).loopMap

/-- The original S down-functor with its actual canonical Q zero root. -/
public def mixedOriginalQDownWeakMapS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :
    ContinuousMap.WeaklyPointed (NQReal.basepoint (mixedOriginalQWorkingCategoryS.{uR, uS, uMR,
      uMS, uNR, uNS} S)) (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)) :=
  QuillenMixedUniverseTransport.mixedNQWeaklyPointedMap
    (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uS, uMS, max (max uR uMR + 1) (max uS uMS +
    1) uNR uNS, max (max uR uMR) (max uS uMS) uNR uNS} S)

/-- The SAME actual S down-functor on original one-fold Q loop carriers. -/
public def mixedOriginalQDownLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :
    C(NQKSpace (mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S), NQKSpace
      (FGProjectiveCat.{max uS uMS} S)) :=
  (mixedOriginalQDownWeakMapS.{uR, uS, uMR, uMS, uNR, uNS} S).loopMap

end AlgebraicKTheory.StableGL

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.QuillenMixedUniverseTransport

private theorem mixedNQWeaklyPointedMapValueComputed.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasBinaryBiproducts D] [ExactCategory D] (F : C ⥤ D) [F.Additive] [F.IsExact] :
    mixedNQWeaklyPointedMap F =
      (⟨mixedNQRealMap F, mixedNQRootPath F⟩ :
        ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint D)) := by
  rfl

/-- The SAME mixed Q weak map has its entire original map/root constructor value. -/
public theorem mixedNQWeaklyPointedMap_value.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasBinaryBiproducts D] [ExactCategory D] (F : C ⥤ D) [F.Additive] [F.IsExact] :
    mixedNQWeaklyPointedMap F =
      (⟨mixedNQRealMap F, mixedNQRootPath F⟩ :
        ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint D)) :=
  mixedNQWeaklyPointedMapValueComputed F

end AlgebraicKTheory.QuillenMixedUniverseTransport

namespace AlgebraicKTheory.StableGL

private theorem mixedOriginalQUpRLoopValueComputed.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] :
    mixedOriginalQUpLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} R =
      QuillenMixedUniverseTransport.mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} R) := by
  rfl

/-- The whole original UpR loop map is the mixed map of its SAME original up functor. -/
public theorem mixedOriginalQUpLoopMapR_value.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] :
    mixedOriginalQUpLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} R =
      QuillenMixedUniverseTransport.mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} R) :=
  mixedOriginalQUpRLoopValueComputed R

private theorem mixedOriginalQUpSLoopValueComputed.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] :
    mixedOriginalQUpLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} S =
      QuillenMixedUniverseTransport.mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} S) := by
  rfl

/-- The whole original UpS loop map is the mixed map of its SAME original up functor. -/
public theorem mixedOriginalQUpLoopMapS_value.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] :
    mixedOriginalQUpLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} S =
      QuillenMixedUniverseTransport.mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} S) :=
  mixedOriginalQUpSLoopValueComputed S

private theorem mixedOriginalQDownRLoopValueComputed.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] :
    mixedOriginalQDownLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} R =
      QuillenMixedUniverseTransport.mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uMR,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} R) := by
  rfl

/-- The whole original DownR loop map is the mixed map of its SAME original down functor. -/
public theorem mixedOriginalQDownLoopMapR_value.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] :
    mixedOriginalQDownLoopMapR.{uR, uS, uMR, uMS, uNR, uNS} R =
      QuillenMixedUniverseTransport.mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uMR,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} R) :=
  mixedOriginalQDownRLoopValueComputed R

private theorem mixedOriginalQDownSLoopValueComputed.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] :
    mixedOriginalQDownLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} S =
      QuillenMixedUniverseTransport.mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uS, uMS,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} S) := by
  rfl

/-- The whole original DownS loop map is the mixed map of its SAME original down functor. -/
public theorem mixedOriginalQDownLoopMapS_value.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] :
    mixedOriginalQDownLoopMapS.{uR, uS, uMR, uMS, uNR, uNS} S =
      QuillenMixedUniverseTransport.mixedNQKSpaceMap
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uS, uMS,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} S) :=
  mixedOriginalQDownSLoopValueComputed S

end AlgebraicKTheory.StableGL

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.QuillenMixedUniverseTransport

private theorem mixedNQKSpaceMapWholeWeakValueComputed.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasBinaryBiproducts D] [ExactCategory D] (F : C ⥤ D) [F.Additive] [F.IsExact] :
    mixedNQKSpaceMap F = (mixedNQWeaklyPointedMap F).loopMap := by
  rfl

/-- The WHOLE original NQ loop map is the loop map of its SAME actual weak map and zero root. -/
public theorem mixedNQKSpaceMap_wholeWeak_value.{uC, vC, uD, vD}
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasBinaryBiproducts D] [ExactCategory D] (F : C ⥤ D) [F.Additive] [F.IsExact] :
    mixedNQKSpaceMap F = (mixedNQWeaklyPointedMap F).loopMap :=
  mixedNQKSpaceMapWholeWeakValueComputed F

end AlgebraicKTheory.QuillenMixedUniverseTransport

end

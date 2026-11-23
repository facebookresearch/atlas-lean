/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.ExactCategoryFunctor
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedQRoot
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedStageRoot
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv
public import MathlibExt.KTheory.Exact.Quillen.QuillenOriginalZigzagBasedInverse
public import MathlibExt.Topology.Homotopy.OriginalLoopSquareOwnUnit

/-!
# Actual original mixed grid/Q/Stage whole loop squares

The original weak grid map uses its SAME chosen three-edge root. The exact
mixed whole-map squares and BOTH original root projection homotopies compare
its composites with the original Q/Stage weak maps. Original weak composition
families produce jointly continuous whole loop-square homotopies.
Actual OWNunit compatibility and full inverse-family attachment remain required.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe uC vC uD vD uX uY

namespace AlgebraicKTheory

private theorem originalWeakMapEqFromWholeValues
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : ContinuousMap.WeaklyPointed x y)
    (h : f.hom = g.hom)
    (hr : ∀ t, f.rootPath.toContinuousMap.toFun t = g.rootPath.toContinuousMap.toFun t) : f = g := by
  rcases f with ⟨f, p⟩
  rcases g with ⟨g, q⟩
  cases h
  have hp : p = q := by
    apply Path.ext
    funext t
    exact hr t
  cases hp
  rfl

private def originalLoopSquareOfEqualWholeMaps
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : ContinuousMap.WeaklyPointed x y)
    (h : f.hom = g.hom)
    (hr : f.rootPath.Homotopic
      (g.rootPath.cast (congrArg (fun M : C(X, Y) => M x) h) rfl)) :
    ContinuousMap.Homotopy f.loopMap g.loopMap := by
  rcases f with ⟨f, p⟩
  rcases g with ⟨g, q⟩
  dsimp only at h hr
  cases h
  exact ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy f hr.some

private theorem originalEqualWholeMapsLoopTrace
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : ContinuousMap.WeaklyPointed x y)
    (h : f.hom = g.hom)
    (hr : f.rootPath.Homotopic
      (g.rootPath.cast (congrArg (fun M : C(X, Y) => M x) h) rfl)) :
    ((originalLoopSquareOfEqualWholeMaps f g h hr).evalAt (Path.refl x)).Homotopic
      ((ContinuousMap.WeaklyPointed.loopUnitRootPath f).trans
        (ContinuousMap.WeaklyPointed.loopUnitRootPath g).symm) := by
  rcases f with ⟨f, p⟩
  rcases g with ⟨g, q⟩
  dsimp only at h hr
  cases h
  have H := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy_unitTrace_homotopic f hr.some
  obtain ⟨K⟩ := H
  refine ⟨K.cast rfl ?_⟩
  apply Path.ext
  funext t
  have hF := ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201
    (⟨f, p⟩ : ContinuousMap.WeaklyPointed x y)
  have hG := ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201
    (⟨f, q⟩ : ContinuousMap.WeaklyPointed x y)
  rw [hF, hG]
  rfl

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The standard Waldhausen structure on the original exact category `C`. -/
local instance originalMixedLoopSquareWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
/-- The standard Waldhausen structure on the original exact category `D`. -/
local instance originalMixedLoopSquareWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- The actual original mixed grid map with SAME chosen three-edge zero root. -/
def quillenStageGridDiagonalMixedWeaklyPointed :
    ContinuousMap.WeaklyPointed (quillenStageGridDiagonalReal.basepoint C)
      (quillenStageGridDiagonalReal.basepoint D) :=
  ⟨quillenStageGridDiagonalRealMixedMap F, quillenStageGridDiagonalMixedZeroRoot F⟩

/-- The actual original loop map of the mixed grid functor/root. -/
def quillenStageGridDiagonalMixedLoopMap :
    C(quillenStageGridDiagonalKSpace C, quillenStageGridDiagonalKSpace D) :=
  (quillenStageGridDiagonalMixedWeaklyPointed F).loopMap

private theorem originalReflexiveSuffix
    {X : Type uX} [TopologicalSpace X] {a b c : X} (p : Path a b) (h : b = c) :
    (p.trans ((Path.refl c).cast h rfl)).Homotopic (p.cast rfl h.symm) := by
  cases h
  exact Path.Homotopic.trans_refl p

private theorem originalReflexivePrefix
    {X : Type uX} [TopologicalSpace X] {a b c : X} (p : Path b c) (h : a = b) :
    (((Path.refl b).cast h rfl).trans p).Homotopic (p.cast h rfl) := by
  cases h
  exact Path.Homotopic.refl_trans p

private theorem originalMixedQWeakMapSquare :
    ((quillenStageGridDiagonalMixedWeaklyPointed F).comp
      (quillenStageGridToNQWeaklyPointed (C := D))).hom =
    ((quillenStageGridToNQWeaklyPointed (C := C)).comp
      (NQRealFunctorWeaklyPointed F)).hom := by
  rw [ContinuousMap.WeaklyPointed.comp_hom, ContinuousMap.WeaklyPointed.comp_hom,
    NQRealFunctorWeaklyPointed_hom]
  exact quillenStageGridToNQ_mixed_realization_square F

private theorem originalMixedQCompositeRoot :
    let A := (quillenStageGridDiagonalMixedWeaklyPointed F).comp
      (quillenStageGridToNQWeaklyPointed (C := D))
    let B := (quillenStageGridToNQWeaklyPointed (C := C)).comp (NQRealFunctorWeaklyPointed F)
    A.rootPath.Homotopic (B.rootPath.cast
      (congrArg (fun M : C(quillenStageGridDiagonalReal C, NQReal D) =>
        M (quillenStageGridDiagonalReal.basepoint C))
          (originalMixedQWeakMapSquare F)) rfl) := by
  let p := quillenStageGridDiagonalMixedZeroRoot F
  let q := (NQRealFunctorWeaklyPointed F).rootPath
  let f := (SSet.toTop.map (quillenStageGridToNQ (C := D))).hom
  let x := quillenStageGridDiagonalReal.basepoint C
  let e := quillenStageGridToNQ_map_basepoint C
  let d := quillenStageGridToNQ_map_basepoint D
  let hMaps := quillenStageGridToNQ_mixed_realization_square F
  have hBase : f (quillenStageGridDiagonalRealMixedMap F x) =
      (NQRealFunctorWeaklyPointed F).hom
        ((SSet.toTop.map (quillenStageGridToNQ (C := C))).hom x) := by
    have h := congrArg (fun M : C(quillenStageGridDiagonalReal C, NQReal D) => M x) hMaps
    exact h.trans (congrArg
      (fun M : C(NQReal C, NQReal D) =>
        M ((SSet.toTop.map (quillenStageGridToNQ (C := C))).hom x))
      (NQRealFunctorWeaklyPointed_hom F)).symm
  let hp := hBase.trans (congrArg (NQRealFunctorWeaklyPointed F).hom e)
  have hProj := quillenStageGridDiagonalMixedZeroRoot_toNQ_homotopic F
  have hRaw : ((p.map f.continuous).cast hp.symm d.symm).Homotopic q := hProj
  have hRaw'₀ := hRaw.pathCast hp rfl
  have hCancel : (((p.map f.continuous).cast hp.symm d.symm).cast hp rfl) =
      (p.map f.continuous).cast rfl d.symm := by
    apply Path.ext
    funext t
    rfl
  obtain ⟨R⟩ := hRaw'₀
  have hRaw' : ((p.map f.continuous).cast rfl d.symm).Homotopic (q.cast hp rfl) :=
    ⟨R.cast hCancel rfl⟩
  have hLeft := originalReflexiveSuffix (p.map f.continuous) d
  have hRight := originalReflexivePrefix q (congrArg (NQRealFunctorWeaklyPointed F).hom e)
  have hRight' := hRight.symm.pathCast hBase rfl
  obtain ⟨K⟩ := hLeft.trans hRaw'
  have hRightSource : q.cast hp rfl =
      ((q.cast (congrArg (NQRealFunctorWeaklyPointed F).hom e) rfl).cast hBase rfl) := by
    apply Path.ext
    funext t
    rfl
  have hK : ((p.map f.continuous).trans ((Path.refl (NQReal.basepoint D)).cast d rfl)).Homotopic
      ((q.cast (congrArg (NQRealFunctorWeaklyPointed F).hom e) rfl).cast hBase rfl) :=
    ⟨K.cast rfl hRightSource⟩
  have hFinal := hK.trans hRight'
  obtain ⟨L⟩ := hFinal
  refine ⟨L.cast rfl ?_⟩
  apply Path.ext
  funext t
  rfl

/-- One WHOLE jointly continuous square of the original mixed grid loop map
and EXACT original Quillen K-space functor map, with original leg roots. -/
def quillenStageGridToNQMixedLoopSquare :
    ContinuousMap.Homotopy
      ((quillenStageGridToNQLoopMap (C := D)).comp (quillenStageGridDiagonalMixedLoopMap F))
      ((NQKSpaceFunctorMap F).comp (quillenStageGridToNQLoopMap (C := C))) := by
  let a := quillenStageGridDiagonalMixedWeaklyPointed F
  let qC := quillenStageGridToNQWeaklyPointed (C := C)
  let qD := quillenStageGridToNQWeaklyPointed (C := D)
  let f := NQRealFunctorWeaklyPointed F
  let H := originalLoopSquareOfEqualWholeMaps (a.comp qD) (qC.comp f)
    (originalMixedQWeakMapSquare F) (originalMixedQCompositeRoot F)
  have hQ : f.loopMap = NQKSpaceFunctorMap F := by
    apply ContinuousMap.ext
    intro gamma
    exact (ContinuousMap.WeaklyPointed.loopMap_apply f gamma).trans
      (NQKSpaceFunctorMap_apply F gamma).symm
  let K := (ContinuousMap.WeaklyPointed.loopMapCompHomotopy a qD).symm.trans
    (H.trans (ContinuousMap.WeaklyPointed.loopMapCompHomotopy qC f))
  exact K.cast rfl (congrArg
    (fun M : C(NQKSpace C, NQKSpace D) => M.comp qC.loopMap) hQ)

private theorem originalMixedStageWeakMapSquare :
    ((quillenStageGridDiagonalMixedWeaklyPointed F).comp
      (quillenStageGridToStageWeaklyPointed (C := D))).hom =
    ((quillenStageGridToStageWeaklyPointed (C := C)).comp
      (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed).hom := by
  have hGrid : (quillenStageGridDiagonalMixedWeaklyPointed F).hom =
      quillenStageGridDiagonalRealMixedMap F := rfl
  rw [ContinuousMap.WeaklyPointed.comp_hom, ContinuousMap.WeaklyPointed.comp_hom,
    quillenStageGridToStageWeaklyPointed_hom (C := D),
    quillenStageGridToStageWeaklyPointed_hom (C := C),
    (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed_hom,
    hGrid]
  exact quillenStageGridToStage_mixed_realization_square F

private theorem originalMixedStageCompositeRoot :
    let A := (quillenStageGridDiagonalMixedWeaklyPointed F).comp
      (quillenStageGridToStageWeaklyPointed (C := D))
    let B := (quillenStageGridToStageWeaklyPointed (C := C)).comp
      (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed
    A.rootPath.Homotopic (B.rootPath.cast
      (congrArg (fun M : C(quillenStageGridDiagonalReal C, stageWeakDiagonalReal D) =>
        M (quillenStageGridDiagonalReal.basepoint C))
          (originalMixedStageWeakMapSquare F)) rfl) := by
  let p := quillenStageGridDiagonalMixedZeroRoot F
  let q := (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedRootPath
  let f := (SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := D))).hom
  let x := quillenStageGridDiagonalReal.basepoint C
  let e := (quillenStageGridToStageWeakDiagonal_realizedZeroVertex (C := C)).trans
    (stageWeakDiagonalReal.basepoint_eq_realizedVertex C).symm
  let d := (quillenStageGridToStageWeakDiagonal_realizedZeroVertex (C := D)).trans
    (stageWeakDiagonalReal.basepoint_eq_realizedVertex D).symm
  let hMaps := quillenStageGridToStage_mixed_realization_square F
  let hBase := congrArg
    (fun M : C(quillenStageGridDiagonalReal C, stageWeakDiagonalReal D) => M x) hMaps
  let hp := hBase.trans
    (congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap e)
  have hRaw : ((p.map f.continuous).cast hp.symm d.symm).Homotopic q :=
    quillenStageGridDiagonalMixedZeroRoot_toStage_homotopic F
  let hCMap := congrArg
    (fun M : C(quillenStageGridDiagonalReal C, stageWeakDiagonalReal C) => M x)
    (quillenStageGridToStageWeaklyPointed_hom (C := C))
  let hDMap := congrArg
    (fun M : C(quillenStageGridDiagonalReal D, stageWeakDiagonalReal D) =>
      M (quillenStageGridDiagonalReal.basepoint D))
    (quillenStageGridToStageWeaklyPointed_hom (C := D))
  have hD : ((quillenStageGridToStageWeaklyPointed (C := D)).rootPath.cast
      hDMap.symm rfl) =
      (Path.refl (stageWeakDiagonalReal.basepoint D)).cast d rfl := by
    apply Path.ext
    funext t
    exact quillenOriginalStageZigzag_root_constant D t
  have hC : ((quillenStageGridToStageWeaklyPointed (C := C)).rootPath.cast
      hCMap.symm rfl) =
      (Path.refl (stageWeakDiagonalReal.basepoint C)).cast e rfl := by
    apply Path.ext
    funext t
    exact quillenOriginalStageZigzag_root_constant C t
  have hRaw'₀ := hRaw.pathCast hp rfl
  have hCancel : (((p.map f.continuous).cast hp.symm d.symm).cast hp rfl) =
      (p.map f.continuous).cast rfl d.symm := by
    apply Path.ext
    funext t
    rfl
  obtain ⟨R⟩ := hRaw'₀
  have hRaw' : ((p.map f.continuous).cast rfl d.symm).Homotopic (q.cast hp rfl) :=
    ⟨R.cast hCancel rfl⟩
  have hLeft := originalReflexiveSuffix (p.map f.continuous) d
  have hRight := originalReflexivePrefix q
    (congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap e)
  have hPrefix :
      (((quillenStageGridToStageWeaklyPointed (C := C)).rootPath.map
        (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap.continuous).cast
          (congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
            hCMap).symm rfl) =
      (Path.refl ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
        (stageWeakDiagonalReal.basepoint C))).cast
          (congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap e) rfl := by
    apply Path.ext
    funext t
    exact congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
      (quillenOriginalStageZigzag_root_constant C t)
  have hRight' := hRight.symm.pathCast hBase rfl
  obtain ⟨K⟩ := hLeft.trans hRaw'
  have hRightSource : q.cast hp rfl =
      ((q.cast (congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap e)
        rfl).cast hBase rfl) := by
    apply Path.ext
    funext t
    rfl
  have hK : ((p.map f.continuous).trans
      ((Path.refl (stageWeakDiagonalReal.basepoint D)).cast d rfl)).Homotopic
      ((q.cast (congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap e)
        rfl).cast hBase rfl) := ⟨K.cast rfl hRightSource⟩
  obtain ⟨L⟩ := hK.trans hRight'
  have hSource :
      ((quillenStageGridDiagonalMixedWeaklyPointed F).comp
        (quillenStageGridToStageWeaklyPointed (C := D))).hom x =
      f (quillenStageGridDiagonalRealMixedMap F x) := by
    rw [ContinuousMap.WeaklyPointed.comp_hom, quillenStageGridToStageWeaklyPointed_hom]
    rfl
  let R := L.pathCast hSource rfl
  refine ⟨R.cast ?_ ?_⟩
  · apply Path.ext
    funext t
    change (((p.map f.continuous).trans
      ((Path.refl (stageWeakDiagonalReal.basepoint D)).cast d rfl)).toContinuousMap.toFun t) =
      (((quillenStageGridDiagonalMixedWeaklyPointed F).comp
        (quillenStageGridToStageWeaklyPointed (C := D))).rootPath).toContinuousMap.toFun t
    rw [ContinuousMap.WeaklyPointed.comp_rootPath]
    change (((p.map f.continuous).trans
      ((Path.refl (stageWeakDiagonalReal.basepoint D)).cast d rfl)).toContinuousMap.toFun t) =
      (((p.map (quillenStageGridToStageWeaklyPointed (C := D)).hom.continuous).trans
        (quillenStageGridToStageWeaklyPointed (C := D)).rootPath).toContinuousMap.toFun t)
    have hRawTime : ((p.map f.continuous).trans
        ((Path.refl (stageWeakDiagonalReal.basepoint D)).cast d rfl)).toContinuousMap.toFun t =
        _ := Path.trans_apply (p.map f.continuous)
          ((Path.refl (stageWeakDiagonalReal.basepoint D)).cast d rfl) t
    have hActualTime :
        ((p.map (quillenStageGridToStageWeaklyPointed (C := D)).hom.continuous).trans
          (quillenStageGridToStageWeaklyPointed (C := D)).rootPath).toContinuousMap.toFun t =
        _ := Path.trans_apply
          (p.map (quillenStageGridToStageWeaklyPointed (C := D)).hom.continuous)
          (quillenStageGridToStageWeaklyPointed (C := D)).rootPath t
    rw [hRawTime, hActualTime]
    split_ifs
    · exact (congrArg
        (fun M : C(quillenStageGridDiagonalReal D, stageWeakDiagonalReal D) => M (p _))
        (quillenStageGridToStageWeaklyPointed_hom (C := D))).symm
    · exact (congrArg
        (fun r : Path (f (quillenStageGridDiagonalReal.basepoint D))
          (stageWeakDiagonalReal.basepoint D) => r.toContinuousMap.toFun _) hD).symm
  · apply Path.ext
    funext t
    change ((((Path.refl
      ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
        (stageWeakDiagonalReal.basepoint C))).cast
          (congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap e)
          rfl).trans q).toContinuousMap.toFun t) =
      (((quillenStageGridToStageWeaklyPointed (C := C)).comp
        (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed).rootPath
          ).toContinuousMap.toFun t
    rw [ContinuousMap.WeaklyPointed.comp_rootPath]
    have hRawTime :
        (((Path.refl
          ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
            (stageWeakDiagonalReal.basepoint C))).cast
              (congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap e)
              rfl).trans q).toContinuousMap.toFun t = _ :=
      Path.trans_apply
        ((Path.refl
          ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
            (stageWeakDiagonalReal.basepoint C))).cast
              (congrArg (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap e) rfl)
        q t
    have hActualTime :
        (((quillenStageGridToStageWeaklyPointed (C := C)).rootPath.map
          (map_continuous
            (Functor.IsWaldhausenExact.ofExactCategory
              F).stageWeakDiagonalRealMixedMapWeaklyPointed.hom)).trans
          (Functor.IsWaldhausenExact.ofExactCategory
            F).stageWeakDiagonalRealMixedMapWeaklyPointed.rootPath).toContinuousMap.toFun t = _ :=
      Path.trans_apply
        ((quillenStageGridToStageWeaklyPointed (C := C)).rootPath.map
          (map_continuous
            (Functor.IsWaldhausenExact.ofExactCategory
              F).stageWeakDiagonalRealMixedMapWeaklyPointed.hom))
        (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed.rootPath t
    rw [hRawTime, hActualTime]
    split_ifs
    · exact (congrArg
        (fun r : Path
          ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
            ((SSet.toTop.map (quillenStageGridToStageWeakDiagonal (C := C))).hom x))
          ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
            (stageWeakDiagonalReal.basepoint C)) => r.toContinuousMap.toFun _) hPrefix).symm.trans
        (DFunLike.congr_fun
          (Eq.symm
            ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed_hom))
          ((quillenStageGridToStageWeaklyPointed (C := C)).rootPath.toContinuousMap.toFun _))
    · exact congrFun
        (congrArg
          (fun r : Path
            ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed.hom
              (stageWeakDiagonalReal.basepoint C))
            (stageWeakDiagonalReal.basepoint D) => r.toContinuousMap.toFun)
          (Eq.symm
            ((Functor.IsWaldhausenExact.ofExactCategory
              F).stageWeakDiagonalRealMixedMapWeaklyPointed_rootPath))) _

/-- One WHOLE jointly continuous original mixed grid/Stage loop square,
using the SAME original Stage mixed map/root and chosen grid root. -/
def quillenStageGridToStageMixedLoopSquare :
    ContinuousMap.Homotopy
      ((quillenStageGridToStageLoopMap (C := D)).comp (quillenStageGridDiagonalMixedLoopMap F))
      (((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap).comp
        (quillenStageGridToStageLoopMap (C := C))) := by
  let a := quillenStageGridDiagonalMixedWeaklyPointed F
  let sC := quillenStageGridToStageWeaklyPointed (C := C)
  let sD := quillenStageGridToStageWeaklyPointed (C := D)
  let f := (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed
  let H := originalLoopSquareOfEqualWholeMaps (a.comp sD) (sC.comp f)
    (originalMixedStageWeakMapSquare F) (originalMixedStageCompositeRoot F)
  have hS : f.loopMap = (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap :=
    ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap_eq).symm
  let K := (ContinuousMap.WeaklyPointed.loopMapCompHomotopy a sD).symm.trans
    (H.trans (ContinuousMap.WeaklyPointed.loopMapCompHomotopy sC f))
  exact K.cast rfl (congrArg
    (fun M : C(stageWeakDiagonalKSpace C, stageWeakDiagonalKSpace D) => M.comp sC.loopMap) hS)


private theorem originalCompTrace081
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z}
    (f : ContinuousMap.WeaklyPointed x y) (g : ContinuousMap.WeaklyPointed y z) :
    ((ContinuousMap.WeaklyPointed.loopMapCompHomotopy f g).evalAt (Path.refl x)).Homotopic
      ((ContinuousMap.WeaklyPointed.loopUnitRootPath (f.comp g)).trans
        (((ContinuousMap.WeaklyPointed.loopUnitRootPath f).map g.loopMap.continuous).trans
          (ContinuousMap.WeaklyPointed.loopUnitRootPath g)).symm) := by
  have h := ContinuousMap.WeaklyPointed.loopMapCompHomotopy_unitTrace_homotopic f g
  obtain ⟨K⟩ := h
  refine ⟨K.cast rfl ?_⟩
  apply Path.ext
  funext t
  have hF := ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201 f
  have hG := ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201 g
  have hM := ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201 (f.comp g)
  rw [hF, hG, hM]
  rfl

private theorem originalMixedQSquareTargetPoint
    (gamma : quillenStageGridDiagonalKSpace C) :
    ((NQKSpaceFunctorMap F).comp (quillenStageGridToNQLoopMap (C := C))) gamma =
      (NQRealFunctorWeaklyPointed F).loopMap
        ((quillenStageGridToNQWeaklyPointed (C := C)).loopMap gamma) := by
  exact (NQKSpaceFunctorMap_apply F _).trans
    (ContinuousMap.WeaklyPointed.loopMap_apply (NQRealFunctorWeaklyPointed F) _).symm

private theorem originalMixedStageSquareTargetPoint
    (gamma : quillenStageGridDiagonalKSpace C) :
    (((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap).comp
      (quillenStageGridToStageLoopMap (C := C))) gamma =
    (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed.loopMap
      ((quillenStageGridToStageWeaklyPointed (C := C)).loopMap gamma) := by
  exact congrArg
    (fun M : C(stageWeakDiagonalKSpace C, stageWeakDiagonalKSpace D) =>
      M ((quillenStageGridToStageWeaklyPointed (C := C)).loopMap gamma))
    ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap_eq)

private theorem originalMixedGridLoopAliasValueComputed :
    quillenStageGridDiagonalMixedLoopMap F =
      (quillenStageGridDiagonalMixedWeaklyPointed F).loopMap := rfl

/-- The entire original grid loop map is exactly the loop map of the
original mixed weak map and its original selected three-edge root. -/
theorem quillenStageGridDiagonalMixedLoopMap_eq_loopMap :
    quillenStageGridDiagonalMixedLoopMap F =
      (quillenStageGridDiagonalMixedWeaklyPointed F).loopMap :=
  originalMixedGridLoopAliasValueComputed F

/-- The ACTUAL Q loop square has its source/target total units constructed
from exact original081 paths, with actual middle root trace and both composition triangles. -/
theorem quillenStageGridToNQMixedLoopSquare_OWNunit :
    let a := quillenStageGridDiagonalMixedWeaklyPointed F
    let qC := quillenStageGridToNQWeaklyPointed (C := C)
    let qD := quillenStageGridToNQWeaklyPointed (C := D)
    let f := NQRealFunctorWeaklyPointed F
    let Us := ((ContinuousMap.WeaklyPointed.loopUnitRootPath a).map qD.loopMap.continuous).trans
      (ContinuousMap.WeaklyPointed.loopUnitRootPath qD)
    let Ut := ((ContinuousMap.WeaklyPointed.loopUnitRootPath qC).map f.loopMap.continuous).trans
      (ContinuousMap.WeaklyPointed.loopUnitRootPath f)
    (((quillenStageGridToNQMixedLoopSquare F).evalAt
      (Path.refl (quillenStageGridDiagonalReal.basepoint C))).trans
        (Ut.cast
          ((NQKSpaceFunctorMap_apply F
            (qC.loopMap (Path.refl (quillenStageGridDiagonalReal.basepoint C)))).trans
            (ContinuousMap.WeaklyPointed.loopMap_apply (NQRealFunctorWeaklyPointed F)
              (qC.loopMap (Path.refl (quillenStageGridDiagonalReal.basepoint C)))).symm)
          rfl)).Homotopic (Us.cast (congrArg qD.loopMap
        (DFunLike.congr_fun (quillenStageGridDiagonalMixedLoopMap_eq_loopMap F)
          (Path.refl (quillenStageGridDiagonalReal.basepoint C)))) rfl) := by
  let a := quillenStageGridDiagonalMixedWeaklyPointed F
  let qC := quillenStageGridToNQWeaklyPointed (C := C)
  let qD := quillenStageGridToNQWeaklyPointed (C := D)
  let f := NQRealFunctorWeaklyPointed F
  let H₁ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy a qD
  let H₂ := originalLoopSquareOfEqualWholeMaps (a.comp qD) (qC.comp f)
    (originalMixedQWeakMapSquare F) (originalMixedQCompositeRoot F)
  let H₃ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy qC f
  let x := Path.refl (quillenStageGridDiagonalReal.basepoint C)
  let y := Path.refl (NQReal.basepoint D)
  let Ua := ContinuousMap.WeaklyPointed.loopUnitRootPath (a.comp qD)
  let Ub := ContinuousMap.WeaklyPointed.loopUnitRootPath (qC.comp f)
  let Us := ((ContinuousMap.WeaklyPointed.loopUnitRootPath a).map qD.loopMap.continuous).trans
    (ContinuousMap.WeaklyPointed.loopUnitRootPath qD)
  let Ut := ((ContinuousMap.WeaklyPointed.loopUnitRootPath qC).map f.loopMap.continuous).trans
    (ContinuousMap.WeaklyPointed.loopUnitRootPath f)
  have h := ContinuousMap.originalThreePieceLoopSquare_OWNunit x y H₁ H₂ H₃ Us Ua Ub Ut
    (originalCompTrace081 a qD)
    (originalEqualWholeMapsLoopTrace (a.comp qD) (qC.comp f)
      (originalMixedQWeakMapSquare F) (originalMixedQCompositeRoot F))
    (originalCompTrace081 qC f)
  obtain ⟨K⟩ := h
  refine ⟨K.cast ?_ rfl⟩
  apply Path.ext
  funext t
  rfl

/-- The ACTUAL Stage loop square likewise carries EXACT original081 total
units, preserving all original mixed Stage/Quillen root/family choices. -/
theorem quillenStageGridToStageMixedLoopSquare_OWNunit :
    let a := quillenStageGridDiagonalMixedWeaklyPointed F
    let sC := quillenStageGridToStageWeaklyPointed (C := C)
    let sD := quillenStageGridToStageWeaklyPointed (C := D)
    let f := (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed
    let Us := ((ContinuousMap.WeaklyPointed.loopUnitRootPath a).map sD.loopMap.continuous).trans
      (ContinuousMap.WeaklyPointed.loopUnitRootPath sD)
    let Ut := ((ContinuousMap.WeaklyPointed.loopUnitRootPath sC).map f.loopMap.continuous).trans
      (ContinuousMap.WeaklyPointed.loopUnitRootPath f)
    (((quillenStageGridToStageMixedLoopSquare F).evalAt
      (Path.refl (quillenStageGridDiagonalReal.basepoint C))).trans
        (Ut.cast (congrArg
          (fun M : C(stageWeakDiagonalKSpace C, stageWeakDiagonalKSpace D) =>
            M ((quillenStageGridToStageWeaklyPointed (C := C)).loopMap
              (Path.refl (quillenStageGridDiagonalReal.basepoint C))))
          ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap_eq))
          rfl)).Homotopic (Us.cast (congrArg sD.loopMap
        (DFunLike.congr_fun (quillenStageGridDiagonalMixedLoopMap_eq_loopMap F)
          (Path.refl (quillenStageGridDiagonalReal.basepoint C)))) rfl) := by
  let a := quillenStageGridDiagonalMixedWeaklyPointed F
  let sC := quillenStageGridToStageWeaklyPointed (C := C)
  let sD := quillenStageGridToStageWeaklyPointed (C := D)
  let f := (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed
  let H₁ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy a sD
  let H₂ := originalLoopSquareOfEqualWholeMaps (a.comp sD) (sC.comp f)
    (originalMixedStageWeakMapSquare F) (originalMixedStageCompositeRoot F)
  let H₃ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy sC f
  let x := Path.refl (quillenStageGridDiagonalReal.basepoint C)
  let y := Path.refl (stageWeakDiagonalReal.basepoint D)
  let Ua := ContinuousMap.WeaklyPointed.loopUnitRootPath (a.comp sD)
  let Ub := ContinuousMap.WeaklyPointed.loopUnitRootPath (sC.comp f)
  let Us := ((ContinuousMap.WeaklyPointed.loopUnitRootPath a).map sD.loopMap.continuous).trans
    (ContinuousMap.WeaklyPointed.loopUnitRootPath sD)
  let Ut := ((ContinuousMap.WeaklyPointed.loopUnitRootPath sC).map f.loopMap.continuous).trans
    (ContinuousMap.WeaklyPointed.loopUnitRootPath f)
  have h := ContinuousMap.originalThreePieceLoopSquare_OWNunit x y H₁ H₂ H₃ Us Ua Ub Ut
    (originalCompTrace081 a sD)
    (originalEqualWholeMapsLoopTrace (a.comp sD) (sC.comp f)
      (originalMixedStageWeakMapSquare F) (originalMixedStageCompositeRoot F))
    (originalCompTrace081 sC f)
  obtain ⟨K⟩ := h
  refine ⟨K.cast ?_ rfl⟩
  apply Path.ext
  funext t
  rfl

end AlgebraicKTheory

end


public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]
/-- The standard Waldhausen structure on the original exact category `C`. -/
local instance originalGridWeakValuesWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
/-- The standard Waldhausen structure on the original exact category `D`. -/
local instance originalGridWeakValuesWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

private theorem originalMixedGridWeakMapValueComputed :
    (quillenStageGridDiagonalMixedWeaklyPointed F).hom =
      quillenStageGridDiagonalRealMixedMap F := rfl

/-- The actual original mixed grid weak map has the whole original mixed
realization map as its hom component. -/
theorem quillenStageGridDiagonalMixedWeaklyPointed_hom :
    (quillenStageGridDiagonalMixedWeaklyPointed F).hom =
      quillenStageGridDiagonalRealMixedMap F :=
  originalMixedGridWeakMapValueComputed F

private theorem originalMixedGridWeakRootValueComputed :
    (quillenStageGridDiagonalMixedWeaklyPointed F).rootPath =
      (quillenStageGridDiagonalMixedZeroRoot F).cast
        (congrArg (fun M => M (quillenStageGridDiagonalReal.basepoint C))
          (originalMixedGridWeakMapValueComputed F)) rfl := rfl

/-- The actual original mixed grid root is precisely the original selected
three-edge path, with only its defining hom-component point cast. -/
theorem quillenStageGridDiagonalMixedWeaklyPointed_rootPath :
    (quillenStageGridDiagonalMixedWeaklyPointed F).rootPath =
      (quillenStageGridDiagonalMixedZeroRoot F).cast
        (congrArg (fun M => M (quillenStageGridDiagonalReal.basepoint C))
          (quillenStageGridDiagonalMixedWeaklyPointed_hom F)) rfl :=
  originalMixedGridWeakRootValueComputed F

end AlgebraicKTheory

end


public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]
/-- The standard Waldhausen structure on the original exact category `C`. -/
local instance originalGridLoopAliasWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
/-- The standard Waldhausen structure on the original exact category `D`. -/
local instance originalGridLoopAliasWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

end AlgebraicKTheory

end

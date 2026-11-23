/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0MixedNaturality
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedQRoot
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedStageRoot
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagGroupNaturality
public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorAllKiMap
public import MathlibExt.Topology.Homotopy.WeaklyPointedHomotopyRel

/-!
# Canonical K-zero naturality of the original mixed Quillen maps

The original mixed Stage-grid map and its three-edge zero root give commuting
squares on loop components for both original zigzag legs. Their existing
component equivalences retain their original algebraic inverses. Combining
these squares with mixed weak-stage K-zero naturality identifies the actual
Quillen functor map, and its degree-zero cube map, with the canonical K-zero
homomorphism across independent category universes.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open ContinuousMap.WeaklyPointed
open scoped Topology

universe uX uY uZ uW uC vC uD vD

namespace AlgebraicKTheory

private theorem eraseConstantTail {X : Type uX} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c)
    (hb : b = c) (hq : ∀ t, q t = c) :
    (p.trans q).Homotopic (p.cast rfl hb.symm) := by
  cases hb
  have h : q = Path.refl b := by
    apply Path.ext
    funext t
    exact hq t
  rw [h]
  exact Path.Homotopic.trans_refl p

private theorem eraseConstantHead {X : Type uX} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c)
    (ha : a = b) (hp : ∀ t, p t = b) :
    (p.trans q).Homotopic (q.cast ha rfl) := by
  cases ha
  have h : p = Path.refl a := by
    apply Path.ext
    funext t
    exact hp t
  rw [h]
  exact Path.Homotopic.refl_trans q

private theorem constantLegSquareComponents
    {X : Type uX} {Y : Type uY} {Z : Type uZ} {W : Type uW}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W]
    {x : X} {y : Y} {z : Z} {w : W}
    (f : ContinuousMap.WeaklyPointed x y) (l : ContinuousMap.WeaklyPointed y w)
    (r : ContinuousMap.WeaklyPointed x z) (g : ContinuousMap.WeaklyPointed z w)
    (hSquare : l.hom.comp f.hom = g.hom.comp r.hom)
    (hl : l.hom y = w) (hr : r.hom x = z)
    (hlValue : ∀ t, l.rootPath t = w) (hrValue : ∀ t, r.rootPath t = z)
    (hProjection :
      let he := DFunLike.congr_fun hSquare x
      let hs := he.trans (congrArg g.hom hr)
      ((f.rootPath.map l.hom.continuous).cast hs.symm hl.symm).Homotopic g.rootPath)
    (a : ZerothHomotopy (LoopSpace X x)) :
    l.loopComponentsMap (f.loopComponentsMap a) =
      g.loopComponentsMap (r.loopComponentsMap a) := by
  let he : (f.comp l).hom x = (r.comp g).hom x := DFunLike.congr_fun hSquare x
  let hs : (f.comp l).hom x = g.hom z := he.trans (congrArg g.hom hr)
  let p := f.rootPath.map l.hom.continuous
  have hLeft : (f.comp l).rootPath.Homotopic (p.cast rfl hl.symm) := by
    rw [ContinuousMap.WeaklyPointed.comp_rootPath]
    exact eraseConstantTail p l.rootPath hl hlValue
  have hProjected : (p.cast rfl hl.symm).Homotopic (g.rootPath.cast hs rfl) := by
    obtain ⟨K⟩ := hProjection
    refine ⟨(K.pathCast hs rfl).cast ?_ rfl⟩
    apply Path.ext
    rfl
  have hRight : (r.comp g).rootPath.Homotopic
      (g.rootPath.cast (congrArg g.hom hr) rfl) := by
    rw [ContinuousMap.WeaklyPointed.comp_rootPath]
    exact eraseConstantHead (r.rootPath.map g.hom.continuous) g.rootPath
      (congrArg g.hom hr) (fun t => congrArg g.hom (hrValue t))
  have hRightCast : ((r.comp g).rootPath.cast he rfl).Homotopic
      (g.rootPath.cast hs rfl) := by
    obtain ⟨K⟩ := hRight
    refine ⟨(K.pathCast he rfl).cast rfl ?_⟩
    apply Path.ext
    rfl
  let H : ContinuousMap.HomotopyRel (f.comp l).hom (r.comp g).hom {x} :=
    (ContinuousMap.HomotopyRel.refl (f.comp l).hom {x}).cast rfl hSquare
  have hRoots : (f.comp l).rootPath.Homotopic
      ((r.comp g).rootPath.cast (H.fst_eq_snd (by simp)) rfl) := by
    have h := hLeft.trans (hProjected.trans hRightCast.symm)
    obtain ⟨K⟩ := h
    refine ⟨K.cast rfl ?_⟩
    apply Path.ext
    rfl
  induction a using ZerothHomotopy.rec with
  | mk gamma =>
    rw [ContinuousMap.WeaklyPointed.loopComponentsMap_mk,
      ContinuousMap.WeaklyPointed.loopComponentsMap_mk,
      ContinuousMap.WeaklyPointed.loopComponentsMap_mk,
      ContinuousMap.WeaklyPointed.loopComponentsMap_mk]
    exact zerothHomotopy_mk_eq_of_pathHomotopic
      ((loopMap_comp_homotopic f l gamma).symm.trans
        ((loopMap_homotopic_of_homotopyRel (f.comp l) (r.comp g) H hRoots gamma).trans
          (loopMap_comp_homotopic r g gamma)))

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Standard Waldhausen structure selected locally for the source exact category. -/
local instance : WaldhausenCategory C := ExactCategory.waldhausenCategory C
/-- Standard Waldhausen structure selected locally for the target exact category. -/
local instance : WaldhausenCategory D := ExactCategory.waldhausenCategory D

private def originalMixedGridPointed :
    ContinuousMap.WeaklyPointed (quillenStageGridDiagonalReal.basepoint C)
      (quillenStageGridDiagonalReal.basepoint D) :=
  ⟨quillenStageGridDiagonalRealMixedMap F, quillenStageGridDiagonalMixedZeroRoot F⟩

private theorem originalMixedQComponentSquare
    (a : ZerothHomotopy (quillenStageGridDiagonalKSpace C)) :
    (quillenStageGridToNQWeaklyPointed (C := D)).loopComponentsMap
        ((originalMixedGridPointed F).loopComponentsMap a) =
      (NQRealFunctorWeaklyPointed F).loopComponentsMap
        ((quillenStageGridToNQWeaklyPointed (C := C)).loopComponentsMap a) := by
  let qC := quillenStageGridToNQWeaklyPointed (C := C)
  let qD := quillenStageGridToNQWeaklyPointed (C := D)
  let QF := NQRealFunctorWeaklyPointed F
  have hSquare : qD.hom.comp (originalMixedGridPointed F).hom = QF.hom.comp qC.hom := by
    rw [quillenStageGridToNQWeaklyPointed_hom,
      quillenStageGridToNQWeaklyPointed_hom, NQRealFunctorWeaklyPointed_hom]
    exact quillenStageGridToNQ_mixed_realization_square F
  have hD : qD.hom (quillenStageGridDiagonalReal.basepoint D) = NQReal.basepoint D := by
    rw [quillenStageGridToNQWeaklyPointed_hom]
    exact quillenStageGridToNQ_map_basepoint D
  have hC : qC.hom (quillenStageGridDiagonalReal.basepoint C) = NQReal.basepoint C := by
    rw [quillenStageGridToNQWeaklyPointed_hom]
    exact quillenStageGridToNQ_map_basepoint C
  refine constantLegSquareComponents (originalMixedGridPointed F) qD qC QF
    hSquare hD hC ?_ ?_ ?_ a
  · intro t
    rw [quillenStageGridToNQWeaklyPointed_rootPath]
    rfl
  · intro t
    rw [quillenStageGridToNQWeaklyPointed_rootPath]
    rfl
  · dsimp only
    obtain ⟨K⟩ := quillenStageGridDiagonalMixedZeroRoot_toNQ_homotopic F
    refine ⟨K.cast ?_ rfl⟩
    apply Path.ext
    funext t
    have hValue := DFunLike.congr_fun (quillenStageGridToNQWeaklyPointed_hom D)
      ((quillenStageGridDiagonalMixedZeroRoot F).toContinuousMap.toFun t)
    exact hValue.symm

private theorem originalMixedStageComponentSquare
    (a : ZerothHomotopy (quillenStageGridDiagonalKSpace C)) :
    (quillenStageGridToStageWeaklyPointed (C := D)).loopComponentsMap
        ((originalMixedGridPointed F).loopComponentsMap a) =
      ContinuousMap.WeaklyPointed.loopComponentsMap
        (Functor.IsWaldhausenExact.stageWeakDiagonalRealMixedMapWeaklyPointed
          (Functor.IsWaldhausenExact.ofExactCategory F))
        ((quillenStageGridToStageWeaklyPointed (C := C)).loopComponentsMap a) := by
  let hF := Functor.IsWaldhausenExact.ofExactCategory F
  let sC := quillenStageGridToStageWeaklyPointed (C := C)
  let sD := quillenStageGridToStageWeaklyPointed (C := D)
  let SF := hF.stageWeakDiagonalRealMixedMapWeaklyPointed
  have hSquare : sD.hom.comp (originalMixedGridPointed F).hom = SF.hom.comp sC.hom := by
    rw [quillenStageGridToStageWeaklyPointed_hom,
      quillenStageGridToStageWeaklyPointed_hom,
      Functor.IsWaldhausenExact.stageWeakDiagonalRealMixedMapWeaklyPointed_hom]
    exact quillenStageGridToStage_mixed_realization_square F
  have hD : sD.hom (quillenStageGridDiagonalReal.basepoint D) =
      stageWeakDiagonalReal.basepoint D := by
    rw [quillenStageGridToStageWeaklyPointed_hom]
    exact (quillenStageGridToStageWeakDiagonal_realizedZeroVertex (C := D)).trans
      (stageWeakDiagonalReal.basepoint_eq_realizedVertex D).symm
  have hC : sC.hom (quillenStageGridDiagonalReal.basepoint C) =
      stageWeakDiagonalReal.basepoint C := by
    rw [quillenStageGridToStageWeaklyPointed_hom]
    exact (quillenStageGridToStageWeakDiagonal_realizedZeroVertex (C := C)).trans
      (stageWeakDiagonalReal.basepoint_eq_realizedVertex C).symm
  refine constantLegSquareComponents (originalMixedGridPointed F) sD sC SF
    hSquare hD hC (quillenStageGridToStageWeaklyPointed_rootPath_apply D)
      (quillenStageGridToStageWeaklyPointed_rootPath_apply C) ?_ a
  dsimp only
  obtain ⟨K⟩ := quillenStageGridDiagonalMixedZeroRoot_toStage_homotopic F
  let hHom := congrArg
    (fun f : C(stageWeakDiagonalReal C, stageWeakDiagonalReal D) =>
      f (stageWeakDiagonalReal.basepoint C))
    hF.stageWeakDiagonalRealMixedMapWeaklyPointed_hom
  refine ⟨(K.pathCast hHom rfl).cast ?_ ?_⟩
  · apply Path.ext
    funext t
    have hValue := DFunLike.congr_fun (quillenStageGridToStageWeaklyPointed_hom D)
      ((quillenStageGridDiagonalMixedZeroRoot F).toContinuousMap.toFun t)
    exact hValue.symm
  · rw [hF.stageWeakDiagonalRealMixedMapWeaklyPointed_rootPath]

private theorem originalMixedQK0Square (a : ZerothHomotopy (NQKSpace C)) :
    NQKSpacePiZeroEquivK0 D ((NQRealFunctorWeaklyPointed F).loopComponentsMap a) =
      WaldhausenKTheory.K0.map F (NQKSpacePiZeroEquivK0 C a) := by
  let aRaw : ZerothHomotopy (LoopSpace (NQReal C) (NQReal.basepoint C)) := a
  let QF := NQRealFunctorWeaklyPointed F
  let SF := (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMapWeaklyPointed
  let qC := QuillenQSZigzagGroupNaturality.Internal.quillenStageGridToNQPiZeroEquiv C
  let qD := QuillenQSZigzagGroupNaturality.Internal.quillenStageGridToNQPiZeroEquiv D
  let sC := QuillenQSZigzagGroupNaturality.Internal.quillenStageGridToStagePiZeroEquiv C
  let sD := QuillenQSZigzagGroupNaturality.Internal.quillenStageGridToStagePiZeroEquiv D
  let g := qC.symm aRaw
  have hq : qD ((originalMixedGridPointed F).loopComponentsMap g) =
      QF.loopComponentsMap aRaw :=
    ((quillenStageGridToNQPiZeroEquiv_apply D _).trans
      (originalMixedQComponentSquare F g)).trans
      (congrArg (NQRealFunctorWeaklyPointed F).loopComponentsMap
        ((quillenStageGridToNQPiZeroEquiv_apply C g).symm.trans (qC.apply_symm_apply aRaw)))
  have hqInv : qD.symm (QF.loopComponentsMap aRaw) =
      (originalMixedGridPointed F).loopComponentsMap g := by
    rw [← hq, qD.symm_apply_apply]
  have hStage : sD (qD.symm (QF.loopComponentsMap aRaw)) = SF.loopComponentsMap (sC g) :=
    (congrArg sD hqInv).trans
      ((quillenStageGridToStagePiZeroEquiv_apply D
        ((originalMixedGridPointed F).loopComponentsMap g)).trans
          ((originalMixedStageComponentSquare F g).trans
            (congrArg SF.loopComponentsMap (quillenStageGridToStagePiZeroEquiv_apply C g).symm)))
  have hValueD := NQKSpacePiZeroEquivK0_apply D (QF.loopComponentsMap aRaw)
  have hValueC := NQKSpacePiZeroEquivK0_apply C aRaw
  have hMapped := congrArg (stageWeakDiagonalKSpacePiZeroEquivK0 D) hStage
  have hNaturality := stageWeakDiagonalKSpacePiZeroEquivK0_mixed_naturality F (sC g)
  exact hValueD.trans
    (hMapped.trans (hNaturality.trans (congrArg (WaldhausenKTheory.K0.map F) hValueC).symm))

private theorem originalKFunctorLoopMap :
    NQKSpaceFunctorMap F = (NQRealFunctorWeaklyPointed F).loopMap := by
  apply ContinuousMap.ext
  intro gamma
  exact (NQKSpaceFunctorMap_apply F gamma).trans
    (ContinuousMap.WeaklyPointed.loopMap_apply (NQRealFunctorWeaklyPointed F) gamma).symm

/-- The actual original Quillen functor map has the canonical K-zero value
on every loop component, in independent object and morphism universes. -/
theorem NQKSpaceFunctorPiZeroEquivK0_naturality (a : ZerothHomotopy (NQKSpace C)) :
    NQKSpacePiZeroEquivK0 D
        (ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (NQKSpaceFunctorMap F x))
          (fun {_ _} p => ZerothHomotopy.sound
            (p.map (NQKSpaceFunctorMap F).continuous)) a) =
      WaldhausenKTheory.K0.map F (NQKSpacePiZeroEquivK0 C a) := by
  have h : ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (NQKSpaceFunctorMap F x))
      (fun {_ _} p => ZerothHomotopy.sound (p.map (NQKSpaceFunctorMap F).continuous)) a =
      (NQRealFunctorWeaklyPointed F).loopComponentsMap a := by
    induction a using ZerothHomotopy.rec with
    | mk gamma =>
      let gammaRaw : LoopSpace (NQReal C) (NQReal.basepoint C) := gamma
      have hValue := DFunLike.congr_fun (originalKFunctorLoopMap F) gammaRaw
      have hClass := congrArg
        (fun gamma : LoopSpace (NQReal D) (NQReal.basepoint D) => ZerothHomotopy.mk gamma) hValue
      have hComponent := ContinuousMap.WeaklyPointed.loopComponentsMap_mk
        (NQRealFunctorWeaklyPointed F) gammaRaw
      exact hClass.trans hComponent.symm
  exact (congrArg (NQKSpacePiZeroEquivK0 D) h).trans (originalMixedQK0Square F a)

/-- Degree zero of the original cube map is intertwined with the literal
canonical K-zero homomorphism, with all category worlds independent. -/
theorem NQKSpaceFunctorKiMap_zero_K0_naturality
    (a : HomotopyGroup.Pi 0 (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpacePiZeroEquivK0 D
        (HomotopyGroup.pi0EquivZerothHomotopy
          (X := NQKSpace D) (x := Path.refl (NQReal.basepoint D))
          (NQKSpaceFunctorKiMap F 0 a)) =
      WaldhausenKTheory.K0.map F
        (NQKSpacePiZeroEquivK0 C
          (HomotopyGroup.pi0EquivZerothHomotopy
            (X := NQKSpace C) (x := Path.refl (NQReal.basepoint C)) a)) := by
  rw [NQKSpaceFunctorKiMap_zero_components]
  exact NQKSpaceFunctorPiZeroEquivK0_naturality F
    (HomotopyGroup.pi0EquivZerothHomotopy
      (X := NQKSpace C) (x := Path.refl (NQReal.basepoint C)) a)

end AlgebraicKTheory

end

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe u v

namespace AlgebraicKTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C] [ExactCategory D]

/-- In a common category frame, the actual degree-zero cube map agrees on
components with the existing Quillen component map. -/
theorem NQKSpaceFunctorKiMap_zero_components_eq_PiZeroMap
    (F : C ⥤ D) [F.Additive] [F.IsExact]
    (a : HomotopyGroup.Pi 0 (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    HomotopyGroup.pi0EquivZerothHomotopy
        (X := NQKSpace D) (x := Path.refl (NQReal.basepoint D))
        (NQKSpaceFunctorKiMap F 0 a) =
      NQKSpacePiZeroMap F
        (HomotopyGroup.pi0EquivZerothHomotopy
          (X := NQKSpace C) (x := Path.refl (NQReal.basepoint C)) a) := by
  apply (NQKSpacePiZeroEquivK0 D).injective
  rw [NQKSpaceFunctorKiMap_zero_K0_naturality, NQKSpacePiZeroEquivK0_naturality]

end AlgebraicKTheory

end

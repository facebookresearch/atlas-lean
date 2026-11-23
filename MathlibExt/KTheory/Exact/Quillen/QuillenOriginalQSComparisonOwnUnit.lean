/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenOriginalQSInverseOwnUnit
public import MathlibExt.Topology.Homotopy.OriginalCorrectedLoopInverse
public import MathlibExt.KTheory.Exact.Quillen.QuillenOriginalQSLoopComparison
public import MathlibExt.Topology.Homotopy.OriginalLoopSquareOwnUnit
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopMultiplication

/-!
# Basepoint paths and units for the Quillen Q/S comparison

For a preadditive exact category with a zero object and binary biproducts,
this module compares the loop map of the weakly pointed Q/S realization
comparison with `quillenOriginalQSLoopMap`. The realization comparison is
the corrected Q inverse followed by the S-construction map.

The calibration homotopy is compatible with the unit path from the image
of the constant Q-loop to the constant S-loop. The comparison preserves
loop concatenation up to continuous homotopy.

## Main results

* `quillenOriginalQSComparisonWeakMap`: the weakly pointed realization map.
* `quillenOriginalQSComparisonCalibration_OWNunit`: compatibility of the
  calibration homotopy with the unit path.
* `quillenOriginalQSComparisonConcatHomotopy`: compatibility with loop
  concatenation.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe u v

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The standard Waldhausen structure on the original exact category `C`. -/
local instance originalQSComparisonOwnUnitWaldhausen : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- The corrected weakly pointed inverse of the Q-realization equivalence. -/
def quillenOriginalQCorrectedInverseWeakMap :
    ContinuousMap.WeaklyPointed (NQReal.basepoint C) (quillenStageGridDiagonalReal.basepoint C) :=
  ContinuousMap.HomotopyEquiv.originalCorrectedInverseWeakMap
    (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
    (quillenOriginalQForwardRealRoot C)

private theorem originalQCorrectedInverseWeakMapValueComputed :
    quillenOriginalQCorrectedInverseWeakMap C =
      ContinuousMap.HomotopyEquiv.originalCorrectedInverseWeakMap
        (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
        (quillenOriginalQForwardRealRoot C) := rfl

/-- The corrected inverse weak map is the inverse supplied by the
Q-realization equivalence, with its basepoint path. -/
theorem quillenOriginalQCorrectedInverseWeakMap_eq :
    quillenOriginalQCorrectedInverseWeakMap C =
      ContinuousMap.HomotopyEquiv.originalCorrectedInverseWeakMap
        (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
        (quillenOriginalQForwardRealRoot C) :=
  originalQCorrectedInverseWeakMapValueComputed C

/-- The weakly pointed Q/S comparison, formed from the corrected Q inverse
and the S-construction map. -/
def quillenOriginalQSComparisonWeakMap :
    ContinuousMap.WeaklyPointed (NQReal.basepoint C) (stageWeakDiagonalReal.basepoint C) :=
  (quillenOriginalQCorrectedInverseWeakMap C).comp
    (quillenStageGridToStageWeaklyPointed (C := C))

private theorem originalQSComparisonWeakMapValueComputed :
    quillenOriginalQSComparisonWeakMap C =
      (quillenOriginalQCorrectedInverseWeakMap C).comp
        (quillenStageGridToStageWeaklyPointed (C := C)) := rfl

/-- The Q/S comparison is the corrected Q inverse followed by the
S-construction map, with the composed basepoint path. -/
theorem quillenOriginalQSComparisonWeakMap_eq :
    quillenOriginalQSComparisonWeakMap C =
      (quillenOriginalQCorrectedInverseWeakMap C).comp
        (quillenStageGridToStageWeaklyPointed (C := C)) :=
  originalQSComparisonWeakMapValueComputed C

private theorem originalQZigzagLoopInverseOwnRootComputed :
    ((quillenOriginalQZigzagLoopEquiv C).invFun :
      C(NQKSpace C, quillenStageGridDiagonalKSpace C)) =
      ((quillenOriginalQZigzagHomotopyEquiv C).weaklyPointedLoopHomotopyEquiv
        (quillenStageGridDiagonalReal.basepoint C) (quillenOriginalQForwardRealRoot C)).invFun := by
  let E : ContinuousMap.HomotopyEquiv (quillenStageGridDiagonalReal C) (NQReal C) :=
    quillenOriginalQZigzagHomotopyEquiv C
  let x : quillenStageGridDiagonalReal C := quillenStageGridDiagonalReal.basepoint C
  let y : NQReal C := NQReal.basepoint C
  let pLiteral : Path (E.toFun x) y :=
    (quillenStageGridToNQWeaklyPointed (C := C)).rootPath.cast
      (congrArg (fun f => f (quillenStageGridDiagonalReal.basepoint C))
        (quillenOriginalQZigzagHomotopyEquiv_toFun C)) rfl
  have hRoot : quillenOriginalQForwardRealRoot C = pLiteral := by
    apply Path.ext
    funext t
    exact (quillenOriginalQForwardRealRoot_constant C t).trans
      (quillenOriginalQZigzag_root_constant C t).symm
  let R : Path (E.toFun x) y → C(NQKSpace C, quillenStageGridDiagonalKSpace C) :=
    fun p => (E.weaklyPointedLoopHomotopyEquiv x p).invFun
  have hFamily : R (quillenOriginalQForwardRealRoot C) = R pLiteral :=
    congrArg R hRoot
  have hNamed : (quillenOriginalQZigzagLoopEquiv C).invFun = R pLiteral :=
    quillenOriginalQZigzagLoopEquiv_invFun C
  exact hNamed.trans hFamily.symm

/-- The unit path for the corrected Q-loop inverse. -/
def quillenOriginalQCorrectedInverse081Unit :
    Path ((quillenOriginalQZigzagLoopEquiv C).invFun (Path.refl (NQReal.basepoint C)))
      (Path.refl (quillenStageGridDiagonalReal.basepoint C)) := by
  let U := ContinuousMap.HomotopyEquiv.originalCorrectedInverseOwnUnit
    (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
    (quillenOriginalQForwardRealRoot C)
  exact U.cast
    (DFunLike.congr_fun (originalQZigzagLoopInverseOwnRootComputed C)
      (Path.refl (NQReal.basepoint C))) rfl

/-- A homotopy from the corrected inverse's induced loop map to the
Q-loop inverse. -/
def quillenOriginalQCorrectedInverseCalibration :
    ContinuousMap.Homotopy (quillenOriginalQCorrectedInverseWeakMap C).loopMap
      (quillenOriginalQZigzagLoopEquiv C).invFun := by
  let H := ContinuousMap.HomotopyEquiv.originalCorrectedInverseLoopHomotopy
    (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
    (quillenOriginalQForwardRealRoot C)
  exact H.cast
    (congrArg ContinuousMap.WeaklyPointed.loopMap
      (quillenOriginalQCorrectedInverseWeakMap_eq C)).symm
    (originalQZigzagLoopInverseOwnRootComputed C).symm

/-- The path from the image of the constant Q-loop to the constant S-loop,
formed by composing the inverse and S-construction unit paths. -/
def quillenOriginalQSComparisonOwnUnit :
    Path (quillenOriginalQSLoopMap C (Path.refl (NQReal.basepoint C)))
      (Path.refl (stageWeakDiagonalReal.basepoint C)) :=
  (((quillenOriginalQCorrectedInverse081Unit C).map
    (quillenStageGridToStageLoopMap (C := C)).continuous).trans
      (ContinuousMap.WeaklyPointed.loopUnitRootPath
        (quillenStageGridToStageWeaklyPointed (C := C)))).cast
          (congrArg (fun M => M (Path.refl (NQReal.basepoint C)))
            (quillenOriginalQSLoopMap_eq C)) rfl

/-- A homotopy from the weakly pointed realization comparison's loop map
to `quillenOriginalQSLoopMap`. -/
def quillenOriginalQSComparisonCalibration :
    ContinuousMap.Homotopy (quillenOriginalQSComparisonWeakMap C).loopMap
      (quillenOriginalQSLoopMap C) := by
  let q := quillenOriginalQCorrectedInverseWeakMap C
  let s := quillenStageGridToStageWeaklyPointed (C := C)
  let H₁ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy q s
  let H₂ := (ContinuousMap.Homotopy.refl s.loopMap).comp
    (quillenOriginalQCorrectedInverseCalibration C)
  exact H₁.trans (H₂.cast rfl (quillenOriginalQSLoopMap_eq C).symm)

/-- The calibration and comparison unit path agree up to homotopy with the
weakly pointed loop unit path. -/
theorem quillenOriginalQSComparisonCalibration_OWNunit :
    (((quillenOriginalQSComparisonCalibration C).evalAt (Path.refl (NQReal.basepoint C))).trans
      (quillenOriginalQSComparisonOwnUnit C)).Homotopic
        (ContinuousMap.WeaklyPointed.loopUnitRootPath (quillenOriginalQSComparisonWeakMap C)) := by
  let q := quillenOriginalQCorrectedInverseWeakMap C
  let s := quillenStageGridToStageWeaklyPointed (C := C)
  let T₁ := (ContinuousMap.WeaklyPointed.loopMapCompHomotopy q s).evalAt
    (Path.refl (NQReal.basepoint C))
  let T₂ := ((ContinuousMap.Homotopy.refl s.loopMap).comp
    (quillenOriginalQCorrectedInverseCalibration C)).evalAt (Path.refl (NQReal.basepoint C))
  let U := ContinuousMap.WeaklyPointed.loopUnitRootPath (q.comp s)
  let V := ((ContinuousMap.WeaklyPointed.loopUnitRootPath q).map s.loopMap.continuous).trans
    (ContinuousMap.WeaklyPointed.loopUnitRootPath s)
  let W := quillenOriginalQSComparisonOwnUnit C
  have hSource : (quillenOriginalQSComparisonWeakMap C).loopMap
      (Path.refl (NQReal.basepoint C)) = (q.comp s).loopMap (Path.refl (NQReal.basepoint C)) :=
    congrArg (fun Q : ContinuousMap.WeaklyPointed (NQReal.basepoint C)
      (stageWeakDiagonalReal.basepoint C) => Q.loopMap (Path.refl (NQReal.basepoint C)))
        (quillenOriginalQSComparisonWeakMap_eq C)
  have hTarget : quillenOriginalQSLoopMap C (Path.refl (NQReal.basepoint C)) =
      (s.loopMap.comp (quillenOriginalQZigzagLoopEquiv C).invFun)
        (Path.refl (NQReal.basepoint C)) := by
    have hs : (quillenStageGridToStageLoopMap (C := C) :
        C(quillenStageGridDiagonalKSpace C, stageWeakDiagonalKSpace C)) = s.loopMap := by
      apply ContinuousMap.ext
      intro gamma
      change (quillenStageGridToStageWeaklyPointed (C := C)).loopMap gamma =
        (quillenStageGridToStageWeaklyPointed (C := C)).loopMap gamma
      rfl
    have hActual : (quillenOriginalQSLoopMap C :
        C(NQKSpace C, stageWeakDiagonalKSpace C)) =
        s.loopMap.comp (quillenOriginalQZigzagLoopEquiv C).invFun :=
      (quillenOriginalQSLoopMap_eq C).trans
        (congrArg
          (fun f : C(quillenStageGridDiagonalKSpace C, stageWeakDiagonalKSpace C) =>
            f.comp (quillenOriginalQZigzagLoopEquiv C).invFun) hs)
    exact DFunLike.congr_fun hActual (Path.refl (NQReal.basepoint C))
  let W' := W.cast hTarget.symm rfl
  have h₁ : (T₁.trans V).Homotopic U := by
    have h := ContinuousMap.WeaklyPointed.loopMapCompHomotopy_unitTrace_homotopic q s
    obtain ⟨K⟩ := h
    have hTrace : T₁.Homotopic (U.trans V.symm) := by
      refine ⟨K.cast rfl ?_⟩
      apply Path.ext
      funext t
      dsimp only [U, V]
      rw [ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201,
        ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201,
        ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201]
      rfl
    exact (hTrace.hcomp (Path.Homotopic.refl V)).trans
      ((Path.Homotopic.trans_assoc U V.symm V).trans
        (((Path.Homotopic.refl U).hcomp (Path.Homotopic.symm_trans V)).trans
          (Path.Homotopic.trans_refl U)))
  have h₂ : (T₂.trans W').Homotopic V := by
    have h := ContinuousMap.HomotopyEquiv.originalCorrectedInverseLoopHomotopy_OWNunit
      (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
      (quillenOriginalQForwardRealRoot C)
    obtain ⟨K⟩ := h
    have hQ : q.loopMap (Path.refl (NQReal.basepoint C)) =
        (ContinuousMap.HomotopyEquiv.originalCorrectedInverseWeakMap
          (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
          (quillenOriginalQForwardRealRoot C)).loopMap (Path.refl (NQReal.basepoint C)) :=
      congrArg (fun Q : ContinuousMap.WeaklyPointed (NQReal.basepoint C)
        (quillenStageGridDiagonalReal.basepoint C) => Q.loopMap (Path.refl (NQReal.basepoint C)))
          (quillenOriginalQCorrectedInverseWeakMap_eq C)
    let L := (K.pathCast hQ rfl).map s.loopMap
    let R := (quillenOriginalQCorrectedInverse081Unit C).map s.loopMap.continuous
    have hMapped : (T₂.trans R).Homotopic
        ((ContinuousMap.WeaklyPointed.loopUnitRootPath q).map s.loopMap.continuous) := by
      refine ⟨L.cast ?_ ?_⟩
      · apply Path.ext
        funext t
        let HQ := ContinuousMap.HomotopyEquiv.originalCorrectedInverseLoopHomotopy
          (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
          (quillenOriginalQForwardRealRoot C)
        let UQ := ContinuousMap.HomotopyEquiv.originalCorrectedInverseOwnUnit
          (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
          (quillenOriginalQForwardRealRoot C)
        change s.loopMap (((HQ.evalAt (Path.refl (NQReal.basepoint C))).trans UQ) t) =
          (T₂.trans R) t
        have hLeft := congrArg s.loopMap
          (Path.trans_apply (HQ.evalAt (Path.refl (NQReal.basepoint C))) UQ t)
        have hRight := Path.trans_apply T₂ R t
        refine hLeft.trans (Eq.trans ?_ hRight.symm)
        split_ifs
        · dsimp only [T₂, HQ, quillenOriginalQCorrectedInverseCalibration]
          rfl
        · dsimp only [R, UQ, quillenOriginalQCorrectedInverse081Unit]
          rfl
      · apply Path.ext
        funext t
        exact congrArg s.loopMap
          ((congrArg (fun Q : ContinuousMap.WeaklyPointed (NQReal.basepoint C)
            (quillenStageGridDiagonalReal.basepoint C) =>
              (ContinuousMap.WeaklyPointed.loopUnitRootPath Q) t)
                (quillenOriginalQCorrectedInverseWeakMap_eq C)).symm)
    have hW : W' = R.trans (ContinuousMap.WeaklyPointed.loopUnitRootPath s) := by
      apply Path.ext
      funext t
      dsimp only [W', W, R, quillenOriginalQSComparisonOwnUnit, quillenStageGridToStageLoopMap]
      rfl
    have hJoin :
        (T₂.trans (R.trans (ContinuousMap.WeaklyPointed.loopUnitRootPath s))).Homotopic V :=
      (Path.Homotopic.trans_assoc T₂ R (ContinuousMap.WeaklyPointed.loopUnitRootPath s)).symm.trans
        (hMapped.hcomp (Path.Homotopic.refl (ContinuousMap.WeaklyPointed.loopUnitRootPath s)))
    obtain ⟨J⟩ := hJoin
    exact ⟨J.cast (congrArg (fun P => T₂.trans P) hW).symm rfl⟩
  have hTotal : ((T₁.trans T₂).trans W').Homotopic U :=
    (Path.Homotopic.trans_assoc T₁ T₂ W').trans
      (((Path.Homotopic.refl T₁).hcomp h₂).trans h₁)
  have hTrace : (quillenOriginalQSComparisonCalibration C).evalAt
      (Path.refl (NQReal.basepoint C)) = (T₁.trans T₂).cast hSource hTarget := by
    apply Path.ext
    funext t
    let H₁ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy q s
    let H₂ := ((ContinuousMap.Homotopy.refl s.loopMap).comp
      (quillenOriginalQCorrectedInverseCalibration C)).cast rfl (quillenOriginalQSLoopMap_eq C).symm
    have hH := ContinuousMap.Homotopy.trans_apply H₁ H₂
      (t, Path.refl (NQReal.basepoint C))
    have hP := Path.trans_apply T₁ T₂ t
    exact hH.trans hP.symm
  obtain ⟨K⟩ := hTotal
  refine ⟨(K.pathCast hSource rfl).cast ?_ ?_⟩
  · have hP : ((T₁.trans T₂).trans W').cast hSource rfl =
        ((T₁.trans T₂).cast hSource hTarget).trans W := by
      apply Path.ext
      funext t
      rfl
    exact hP.trans (congrArg (fun P => P.trans W) hTrace).symm
  · apply Path.ext
    funext t
    exact (congrArg (fun Q : ContinuousMap.WeaklyPointed (NQReal.basepoint C)
      (stageWeakDiagonalReal.basepoint C) => (ContinuousMap.WeaklyPointed.loopUnitRootPath Q) t)
        (quillenOriginalQSComparisonWeakMap_eq C)).symm



/-- The Q/S loop comparison preserves loop concatenation up to continuous
homotopy. -/
def quillenOriginalQSComparisonConcatHomotopy :
    ContinuousMap.Homotopy
      ((quillenOriginalQSLoopMap C).comp
        (HSpace.hmul : C(NQKSpace C × NQKSpace C, NQKSpace C)))
      ((HSpace.hmul : C(stageWeakDiagonalKSpace C × stageWeakDiagonalKSpace C,
        stageWeakDiagonalKSpace C)).comp
          ((quillenOriginalQSLoopMap C).prodMap (quillenOriginalQSLoopMap C))) := by
  let Q := quillenOriginalQSComparisonWeakMap C
  let M := quillenOriginalQSLoopMap C
  let K := quillenOriginalQSComparisonCalibration C
  let mQ : C(NQKSpace C × NQKSpace C, NQKSpace C) := HSpace.hmul
  let mS : C(stageWeakDiagonalKSpace C × stageWeakDiagonalKSpace C,
    stageWeakDiagonalKSpace C) := HSpace.hmul
  let H₁ := K.symm.compContinuousMap mQ
  let H₂ := ContinuousMap.WeaklyPointed.loopMapMultiplicationHomotopy Q
  let H₃ := (ContinuousMap.Homotopy.refl mS).comp (K.prodMap K)
  exact H₁.trans (H₂.trans H₃)

end AlgebraicKTheory

end

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe u v

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
attribute [local instance] originalQSComparisonOwnUnitWaldhausen

private theorem originalQCorrectedInverseCalibrationTimeComputed
    (t : unitInterval) (gamma : NQKSpace C) :
    (quillenOriginalQCorrectedInverseCalibration C).toContinuousMap.toFun (t, gamma) =
      (ContinuousMap.HomotopyEquiv.originalCorrectedInverseLoopHomotopy
        (quillenOriginalQZigzagHomotopyEquiv C)
        (quillenStageGridDiagonalReal.basepoint C)
        (quillenOriginalQForwardRealRoot C)).toContinuousMap.toFun (t, gamma) := rfl

/-- The corrected-inverse calibration agrees at every time with the
corresponding inverse-loop homotopy. -/
theorem quillenOriginalQCorrectedInverseCalibration_apply
    (t : unitInterval) (gamma : NQKSpace C) :
    (quillenOriginalQCorrectedInverseCalibration C).toContinuousMap.toFun (t, gamma) =
      (ContinuousMap.HomotopyEquiv.originalCorrectedInverseLoopHomotopy
        (quillenOriginalQZigzagHomotopyEquiv C)
        (quillenStageGridDiagonalReal.basepoint C)
        (quillenOriginalQForwardRealRoot C)).toContinuousMap.toFun (t, gamma) :=
  originalQCorrectedInverseCalibrationTimeComputed C t gamma

private theorem originalQCorrectedInverse081UnitTimeComputed
    (t : unitInterval) :
    (quillenOriginalQCorrectedInverse081Unit C).toContinuousMap.toFun t =
      (ContinuousMap.HomotopyEquiv.originalCorrectedInverseOwnUnit
        (quillenOriginalQZigzagHomotopyEquiv C)
        (quillenStageGridDiagonalReal.basepoint C)
        (quillenOriginalQForwardRealRoot C)).toContinuousMap.toFun t := rfl

/-- The corrected-inverse unit path agrees pointwise with its defining
unit path. -/
theorem quillenOriginalQCorrectedInverse081Unit_apply
    (t : unitInterval) :
    (quillenOriginalQCorrectedInverse081Unit C).toContinuousMap.toFun t =
      (ContinuousMap.HomotopyEquiv.originalCorrectedInverseOwnUnit
        (quillenOriginalQZigzagHomotopyEquiv C)
        (quillenStageGridDiagonalReal.basepoint C)
        (quillenOriginalQForwardRealRoot C)).toContinuousMap.toFun t :=
  originalQCorrectedInverse081UnitTimeComputed C t

private theorem originalQSComparisonOwnUnitTimeComputed
    (t : unitInterval) :
    (quillenOriginalQSComparisonOwnUnit C).toContinuousMap.toFun t =
      (((quillenOriginalQCorrectedInverse081Unit C).map
        (quillenStageGridToStageLoopMap (C := C)).continuous).trans
          (ContinuousMap.WeaklyPointed.loopUnitRootPath
            (quillenStageGridToStageWeaklyPointed (C := C)))).toContinuousMap.toFun t := rfl

/-- At each time, the comparison unit is the mapped inverse-unit path
followed by the S-construction unit path. -/
theorem quillenOriginalQSComparisonOwnUnit_apply
    (t : unitInterval) :
    (quillenOriginalQSComparisonOwnUnit C).toContinuousMap.toFun t =
      (((quillenOriginalQCorrectedInverse081Unit C).map
        (quillenStageGridToStageLoopMap (C := C)).continuous).trans
          (ContinuousMap.WeaklyPointed.loopUnitRootPath
            (quillenStageGridToStageWeaklyPointed (C := C)))).toContinuousMap.toFun t :=
  originalQSComparisonOwnUnitTimeComputed C t

end AlgebraicKTheory

end

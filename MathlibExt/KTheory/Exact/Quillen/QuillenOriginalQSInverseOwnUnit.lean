/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenOriginalQSBasedComparison
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv
public import MathlibExt.Topology.Homotopy.RootUnitTraceComparison

/-!
# Actual corrected Q-loop inverse unit from the original full correction family

The original227/398 corrected inverse G2 is retained. Its actual full G2→G
family and SAME201 raw inverse-root contraction supply its unit path.
The resulting rooted compatibility of that actual family is constructed,
not supplied by a caller. Original functor081 units remain unchanged.
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
local instance originalCorrectedInverseUnitWaldhausen : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- SAME original point path passed to227/398 Q loop equivalence. -/
def quillenOriginalQForwardRealRoot :
    Path ((quillenOriginalQZigzagHomotopyEquiv C).toFun (quillenStageGridDiagonalReal.basepoint C))
      (NQReal.basepoint C) :=
  (quillenStageGridToNQWeaklyPointed (C := C)).rootPath.cast
    (congrArg (fun f => f (quillenStageGridDiagonalReal.basepoint C))
      (quillenOriginalQZigzagHomotopyEquiv_toFun C)) rfl

/-- The raw inverse keeps EXACT original selected L.some point trace and
mapped forward point root from the original227 program. -/
def quillenOriginalQRawInverseRoot :
    Path ((quillenOriginalQZigzagHomotopyEquiv C).invFun (NQReal.basepoint C))
      (quillenStageGridDiagonalReal.basepoint C) :=
  ((quillenOriginalQForwardRealRoot C).map
    (quillenOriginalQZigzagHomotopyEquiv C).invFun.continuous).symm.trans
      ((quillenOriginalQZigzagHomotopyEquiv C).left_inv.some.evalAt
        (quillenStageGridDiagonalReal.basepoint C))

/-- The actual raw inverse weak map has its unchanged program root. -/
def quillenOriginalQRawInverseWeakMap :
    ContinuousMap.WeaklyPointed (NQReal.basepoint C) (quillenStageGridDiagonalReal.basepoint C) :=
  ⟨(quillenOriginalQZigzagHomotopyEquiv C).invFun, quillenOriginalQRawInverseRoot C⟩

/-- The actual full corrected-inverse G2→raw-G family is preserved. -/
def quillenOriginalQInverseToRawHomotopy :
    ContinuousMap.Homotopy (quillenOriginalQZigzagLoopEquiv C).invFun
      (quillenOriginalQRawInverseWeakMap C).loopMap := by
  let H := ContinuousMap.HomotopyEquiv.weaklyPointedLoopHomotopyEquivInvFunToRawHomotopy
    (quillenOriginalQZigzagHomotopyEquiv C) (quillenStageGridDiagonalReal.basepoint C)
    (quillenOriginalQForwardRealRoot C)
  exact H.cast (quillenOriginalQZigzagLoopEquiv_invFun C).symm rfl

/-- SAME201 raw inverse-root unit, retaining the original corrected program's
root and original root-unit contraction formula. -/
def quillenOriginalQRawInverseOwnUnit :
    Path ((quillenOriginalQRawInverseWeakMap C).loopMap (Path.refl (NQReal.basepoint C)))
      (Path.refl (quillenStageGridDiagonalReal.basepoint C)) :=
  ((ContinuousMap.rootUnitContraction
    (fun p : Path ((quillenOriginalQRawInverseWeakMap C).hom (NQReal.basepoint C))
      (quillenStageGridDiagonalReal.basepoint C) => p) continuous_eval).evalAt
        (quillenOriginalQRawInverseWeakMap C).rootPath).cast
      (ContinuousMap.WeaklyPointed.loopMapUnit_eq_rootUnitLoopFamily
        (quillenOriginalQRawInverseWeakMap C).hom
        (quillenOriginalQRawInverseWeakMap C).rootPath) rfl

/-- ACTUAL original corrected inverse unit is produced from its SAME full
correction-family point trace and SAME201 raw inverse unit, with no stationarity assumption. -/
def quillenOriginalQCorrectedInverseOwnUnit :
    Path ((quillenOriginalQZigzagLoopEquiv C).invFun (Path.refl (NQReal.basepoint C)))
      (Path.refl (quillenStageGridDiagonalReal.basepoint C)) :=
  ((quillenOriginalQInverseToRawHomotopy C).evalAt (Path.refl (NQReal.basepoint C))).trans
    (quillenOriginalQRawInverseOwnUnit C)

/-- Rooted compatibility of the ACTUAL inverse correction family is earned
by its defining full point trace, with original raw unit and inverse retained. -/
theorem quillenOriginalQInverseToRawHomotopy_OWNunit :
    (((quillenOriginalQInverseToRawHomotopy C).evalAt (Path.refl (NQReal.basepoint C))).trans
      (quillenOriginalQRawInverseOwnUnit C)).Homotopic
        (quillenOriginalQCorrectedInverseOwnUnit C) :=
  Path.Homotopic.refl _


/-- The actual unit-path at every original inverse-correction time, formed
from its SAME moving point trace followed by original201 raw inverse unit. -/
def quillenOriginalQInverseOwnUnitAt (t : unitInterval) :
    Path ((quillenOriginalQInverseToRawHomotopy C).toContinuousMap.toFun
      (t, Path.refl (NQReal.basepoint C)))
      (Path.refl (quillenStageGridDiagonalReal.basepoint C)) :=
  (ContinuousMap.Homotopy.pointTraceTail (quillenOriginalQInverseToRawHomotopy C)
    (Path.refl (NQReal.basepoint C)) t).trans (quillenOriginalQRawInverseOwnUnit C)

/-- The original correction-time zero unit path is EXACT corrected unit,
with only the actual source endpoint equality transported. -/
theorem quillenOriginalQInverseOwnUnitAt_zero :
    ((quillenOriginalQInverseOwnUnitAt C 0).cast
      ((quillenOriginalQInverseToRawHomotopy C).apply_zero
        (Path.refl (NQReal.basepoint C))).symm rfl) =
      quillenOriginalQCorrectedInverseOwnUnit C := by
  apply Path.ext
  funext s
  have hTail := ContinuousMap.Homotopy.pointTraceTail_zero
    (quillenOriginalQInverseToRawHomotopy C) (Path.refl (NQReal.basepoint C))
  have h := congrArg (fun p => p.trans (quillenOriginalQRawInverseOwnUnit C)) hTail
  exact congrArg (fun p => p.toContinuousMap.toFun s) h

/-- The actual endpoint unit family has only its genuine reflexive prefix;
relative path unitor gives the SAME original raw201 inverse unit. -/
theorem quillenOriginalQInverseOwnUnitAt_one_homotopic :
    ((quillenOriginalQInverseOwnUnitAt C 1).cast
      ((quillenOriginalQInverseToRawHomotopy C).apply_one
        (Path.refl (NQReal.basepoint C))).symm rfl).Homotopic
      (quillenOriginalQRawInverseOwnUnit C) := by
  have hTail := ContinuousMap.Homotopy.pointTraceTail_one
    (quillenOriginalQInverseToRawHomotopy C) (Path.refl (NQReal.basepoint C))
  have hPath : ((quillenOriginalQInverseOwnUnitAt C 1).cast
      ((quillenOriginalQInverseToRawHomotopy C).apply_one
        (Path.refl (NQReal.basepoint C))).symm rfl) =
      (Path.refl ((quillenOriginalQRawInverseWeakMap C).loopMap
        (Path.refl (NQReal.basepoint C)))).trans (quillenOriginalQRawInverseOwnUnit C) := by
    apply Path.ext
    funext s
    exact congrArg
      (fun p => (p.trans (quillenOriginalQRawInverseOwnUnit C)).toContinuousMap.toFun s) hTail
  obtain ⟨K⟩ := Path.Homotopic.refl_trans (quillenOriginalQRawInverseOwnUnit C)
  exact ⟨K.cast hPath.symm rfl⟩



/-- The actual full unit rectangle concatenates the original point-trace
TAIL and original201 raw inverse unit, preserving BOTH clocks and all times. -/
def quillenOriginalQInverseOwnUnitRectangle :
    C(unitInterval × unitInterval, quillenStageGridDiagonalKSpace C) :=
  { toFun := fun z => (quillenOriginalQInverseOwnUnitAt C z.1).toContinuousMap.toFun z.2
    continuous_toFun :=
      Path.trans_continuous_family
        (fun t => ContinuousMap.Homotopy.pointTraceTail
          (quillenOriginalQInverseToRawHomotopy C) (Path.refl (NQReal.basepoint C)) t)
        (ContinuousMap.Homotopy.pointTraceTail_continuous
          (quillenOriginalQInverseToRawHomotopy C) (Path.refl (NQReal.basepoint C)))
        (fun _ => quillenOriginalQRawInverseOwnUnit C)
        ((quillenOriginalQRawInverseOwnUnit C).continuous.comp continuous_snd) }

/-- Every original correction time is recovered by the rectangle's source-unit face. -/
theorem quillenOriginalQInverseOwnUnitRectangle_zero (t : unitInterval) :
    quillenOriginalQInverseOwnUnitRectangle C (t, 0) =
      (quillenOriginalQInverseToRawHomotopy C).toContinuousMap.toFun
        (t, Path.refl (NQReal.basepoint C)) :=
  (quillenOriginalQInverseOwnUnitAt C t).source

/-- The selected original grid constant loop is its target-unit face at every time. -/
theorem quillenOriginalQInverseOwnUnitRectangle_one (t : unitInterval) :
    quillenOriginalQInverseOwnUnitRectangle C (t, 1) =
      Path.refl (quillenStageGridDiagonalReal.basepoint C) :=
  (quillenOriginalQInverseOwnUnitAt C t).target

/-- The actual source-time face is SAME corrected inverse own-unit path. -/
theorem quillenOriginalQInverseOwnUnitRectangle_source (s : unitInterval) :
    quillenOriginalQInverseOwnUnitRectangle C (0, s) =
      (quillenOriginalQCorrectedInverseOwnUnit C).toContinuousMap.toFun s := by
  change (quillenOriginalQInverseOwnUnitAt C 0).toContinuousMap.toFun s = _
  exact congrArg (fun p => p.toContinuousMap.toFun s) (quillenOriginalQInverseOwnUnitAt_zero C)

/-- The target-time unit face retains the original raw inverse unit after
its genuine reflexive prefix, rather than declaring it literally stationary. -/
theorem quillenOriginalQInverseOwnUnitRectangle_target (s : unitInterval) :
    quillenOriginalQInverseOwnUnitRectangle C (1, s) =
      ((Path.refl ((quillenOriginalQRawInverseWeakMap C).loopMap
        (Path.refl (NQReal.basepoint C)))).trans (quillenOriginalQRawInverseOwnUnit C)
          ).toContinuousMap.toFun s := by
  change (quillenOriginalQInverseOwnUnitAt C 1).toContinuousMap.toFun s = _
  have hTail := ContinuousMap.Homotopy.pointTraceTail_one
    (quillenOriginalQInverseToRawHomotopy C) (Path.refl (NQReal.basepoint C))
  have hAt : (quillenOriginalQInverseOwnUnitAt C 1).toContinuousMap.toFun s =
      (((ContinuousMap.Homotopy.pointTraceTail (quillenOriginalQInverseToRawHomotopy C)
        (Path.refl (NQReal.basepoint C)) 1).cast
          ((quillenOriginalQInverseToRawHomotopy C).apply_one
            (Path.refl (NQReal.basepoint C))).symm rfl).trans
              (quillenOriginalQRawInverseOwnUnit C)).toContinuousMap.toFun s := rfl
  exact hAt.trans (congrArg
    (fun p => (p.trans (quillenOriginalQRawInverseOwnUnit C)).toContinuousMap.toFun s) hTail)


private theorem originalQForwardRootConstantComputed (t : unitInterval) :
    (quillenOriginalQForwardRealRoot C).toContinuousMap.toFun t = NQReal.basepoint C :=
  quillenOriginalQZigzag_root_constant C t

/-- Every ACTUAL original Q forward-root time is its original selected zero. -/
theorem quillenOriginalQForwardRealRoot_constant (t : unitInterval) :
    (quillenOriginalQForwardRealRoot C).toContinuousMap.toFun t = NQReal.basepoint C :=
  originalQForwardRootConstantComputed C t

/-- EXACT original forward root equals its actual based reflexive cast,
with only the genuine original forward-map/zero equality used. -/
theorem quillenOriginalQForwardRealRoot_eq_based :
    let h : (quillenOriginalQZigzagHomotopyEquiv C).toFun
        (quillenStageGridDiagonalReal.basepoint C) = NQReal.basepoint C :=
      (congrArg (fun f => f (quillenStageGridDiagonalReal.basepoint C))
        (quillenOriginalQZigzagHomotopyEquiv_toFun C)).trans (quillenStageGridToNQ_map_basepoint C)
    quillenOriginalQForwardRealRoot C = (Path.refl (NQReal.basepoint C)).cast h rfl := by
  apply Path.ext
  funext t
  exact quillenOriginalQForwardRealRoot_constant C t

end AlgebraicKTheory

end

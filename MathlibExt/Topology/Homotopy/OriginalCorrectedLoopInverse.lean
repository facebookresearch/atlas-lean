/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv
public import MathlibExt.Topology.Homotopy.OriginalLoopOwnUnitCalibration

/-!
# The SAME original corrected loop inverse has its actual weak-map root

Original G2=G.compJ.invFun and original J.invFun=basepoint-change(d.symm)
retain every L/R.some/p/defect choice. Actual weak composition identifies
G2 with looping the real inverse along its derived defect-corrected root,
and the original composition unit triangle supplies its original081 unit.
No stationary trace, π1 action or inverse outcome is assumed.
-/

public section

noncomputable section

open unitInterval
open scoped Topology

universe u v

namespace ContinuousMap.HomotopyEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- EXACT original raw inverse root from the original selected point trace. -/
def originalRawInverseWeakMap (e : X ≃ₕ Y) (x : X) {y : Y} (p : Path (e.toFun x) y) :
    WeaklyPointed y x :=
  ⟨e.invFun, (p.map e.invFun.continuous).symm.trans (e.left_inv.some.evalAt x)⟩

/-- EXACT original defect loop retained by the original227/398 program. -/
def originalInverseDefectPath (e : X ≃ₕ Y) (x : X) {y : Y} (p : Path (e.toFun x) y) : Path y y :=
  (e.right_inv.some.evalAt y).symm.trans
    (WeaklyPointed.comp (originalRawInverseWeakMap e x p)
      (⟨e.toFun, p⟩ : WeaklyPointed x y)).rootPath

/-- The original inverse defect correction as its actual weak id-map root. -/
def originalInverseDefectWeakMap (e : X ≃ₕ Y) (x : X) {y : Y} (p : Path (e.toFun x) y) :
    WeaklyPointed y y :=
  ⟨ContinuousMap.id Y, (originalInverseDefectPath e x p).symm⟩

/-- The SAME corrected inverse real map is looped along the actual derived
composite defect root; no inverse or root choice is replaced. -/
def originalCorrectedInverseWeakMap (e : X ≃ₕ Y) (x : X) {y : Y} (p : Path (e.toFun x) y) :
    WeaklyPointed y x :=
  WeaklyPointed.comp (originalInverseDefectWeakMap e x p) (originalRawInverseWeakMap e x p)

private theorem originalDefectWeakLoopValueComputed (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) :
    (originalInverseDefectWeakMap e x p).loopMap =
      loopBasepointChange (originalInverseDefectPath e x p).symm := by
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  funext t
  rfl

/-- WHOLE original weak defect correction is the original basepoint-change map. -/
theorem originalInverseDefectWeakMap_loopMap (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) :
    (originalInverseDefectWeakMap e x p).loopMap =
      loopBasepointChange (originalInverseDefectPath e x p).symm :=
  originalDefectWeakLoopValueComputed e x p

private theorem originalCorrectedInverseMapValueComputed (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) :
    (weaklyPointedLoopHomotopyEquiv e x p).invFun =
      (originalRawInverseWeakMap e x p).loopMap.comp (originalInverseDefectWeakMap e x p).loopMap := by
  have h := weaklyPointedLoopHomotopyEquiv_invFun_recipe e x p
  have hJ := loopBasepointChangeHomotopyEquiv_invFun (originalInverseDefectPath e x p)
  have hWeak := originalInverseDefectWeakMap_loopMap e x p
  exact h.trans ((congrArg (fun M => (originalRawInverseWeakMap e x p).loopMap.comp M) hJ).trans
    (congrArg (fun M => (originalRawInverseWeakMap e x p).loopMap.comp M) hWeak.symm))

/-- EXACT original corrected inverse G2 is retained as the original two weak
loop maps in succession, using the original defect correction root. -/
theorem originalCorrectedInverseMap_eq (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) :
    (weaklyPointedLoopHomotopyEquiv e x p).invFun =
      (originalRawInverseWeakMap e x p).loopMap.comp (originalInverseDefectWeakMap e x p).loopMap :=
  originalCorrectedInverseMapValueComputed e x p

/-- The ACTUAL original weak-composition family calibrates the corrected
inverse G2 without changing its values or chosen full inverse families. -/
def originalCorrectedInverseLoopHomotopy (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) :
    Homotopy (originalCorrectedInverseWeakMap e x p).loopMap
      (weaklyPointedLoopHomotopyEquiv e x p).invFun :=
  (WeaklyPointed.loopMapCompHomotopy
    (originalInverseDefectWeakMap e x p) (originalRawInverseWeakMap e x p)).cast rfl
      (originalCorrectedInverseMap_eq e x p).symm

/-- The corrected inverse's actual own-unit retains both original081
component units and the SAME original G2 map endpoint. -/
def originalCorrectedInverseOwnUnit (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) :
    Path ((weaklyPointedLoopHomotopyEquiv e x p).invFun (Path.refl y)) (Path.refl x) :=
  (((WeaklyPointed.loopUnitRootPath (originalInverseDefectWeakMap e x p)).map
      (originalRawInverseWeakMap e x p).loopMap.continuous).trans
        (WeaklyPointed.loopUnitRootPath (originalRawInverseWeakMap e x p))).cast
          (congrArg (fun M => M (Path.refl y)) (originalCorrectedInverseMap_eq e x p)) rfl

/-- The ACTUAL corrected-inverse calibration family is compatible with its
original081 unit path, derived from the actual composition triangle. -/
theorem originalCorrectedInverseLoopHomotopy_OWNunit (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) :
    (((originalCorrectedInverseLoopHomotopy e x p).evalAt (Path.refl y)).trans
      (originalCorrectedInverseOwnUnit e x p)).Homotopic
        (WeaklyPointed.loopUnitRootPath (originalCorrectedInverseWeakMap e x p)) := by
  have h := WeaklyPointed.loopMapCompHomotopy_unitTrace_homotopic
    (originalInverseDefectWeakMap e x p) (originalRawInverseWeakMap e x p)
  obtain ⟨K⟩ := h
  have hInverse :
      (weaklyPointedLoopHomotopyEquiv e x p).invFun (Path.refl y) =
        (originalRawInverseWeakMap e x p).loopMap
          ((originalInverseDefectWeakMap e x p).loopMap (Path.refl y)) :=
    congrArg (fun M => M (Path.refl y)) (originalCorrectedInverseMap_eq e x p)
  let U := WeaklyPointed.loopUnitRootPath (originalCorrectedInverseWeakMap e x p)
  let V := originalCorrectedInverseOwnUnit e x p
  have hTrace : ((originalCorrectedInverseLoopHomotopy e x p).evalAt (Path.refl y)).Homotopic
      (U.trans V.symm) := by
    refine ⟨(K.pathCast rfl hInverse).cast ?_ ?_⟩
    · apply Path.ext
      funext t
      rfl
    · apply Path.ext
      funext t
      dsimp only [U, V, originalCorrectedInverseOwnUnit]
      rw [WeaklyPointed.originalLoopOwnUnit_eq201,
        WeaklyPointed.originalLoopOwnUnit_eq201, WeaklyPointed.originalLoopOwnUnit_eq201]
      rfl
  exact (hTrace.hcomp (Path.Homotopic.refl V)).trans
    ((Path.Homotopic.trans_assoc U V.symm V).trans
      (((Path.Homotopic.refl U).hcomp (Path.Homotopic.symm_trans V)).trans
        (Path.Homotopic.trans_refl U)))

end ContinuousMap.HomotopyEquiv

end


public section

noncomputable section

open scoped Topology

universe u v

namespace ContinuousMap.HomotopyEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

private theorem originalRawInverseRootValueComputed (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) (t : unitInterval) :
    (originalRawInverseWeakMap e x p).rootPath.toContinuousMap.toFun t =
      (((p.map e.invFun.continuous).symm.trans (e.left_inv.some.evalAt x)).toContinuousMap.toFun t) := rfl

/-- Every ACTUAL original raw inverse root time is its SAME selected point-trace program. -/
theorem originalRawInverseWeakMap_rootPath_apply (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) (t : unitInterval) :
    (originalRawInverseWeakMap e x p).rootPath.toContinuousMap.toFun t =
      (((p.map e.invFun.continuous).symm.trans (e.left_inv.some.evalAt x)).toContinuousMap.toFun t) :=
  originalRawInverseRootValueComputed e x p t

private theorem originalInverseDefectValueComputed (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) (t : unitInterval) :
    (originalInverseDefectPath e x p).toContinuousMap.toFun t =
      ((e.right_inv.some.evalAt y).symm.trans
        (((((p.map e.invFun.continuous).symm.trans (e.left_inv.some.evalAt x)).map e.toFun.continuous)
          ).trans p)).toContinuousMap.toFun t := rfl

/-- Every ACTUAL original defect-root time keeps the SAME L/R.some and point path. -/
theorem originalInverseDefectPath_apply (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) (t : unitInterval) :
    (originalInverseDefectPath e x p).toContinuousMap.toFun t =
      ((e.right_inv.some.evalAt y).symm.trans
        (((((p.map e.invFun.continuous).symm.trans (e.left_inv.some.evalAt x)).map e.toFun.continuous)
          ).trans p)).toContinuousMap.toFun t :=
  originalInverseDefectValueComputed e x p t

private theorem originalCorrectedInverseRootValueComputed (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) (t : unitInterval) :
    (originalCorrectedInverseWeakMap e x p).rootPath.toContinuousMap.toFun t =
      (((originalInverseDefectPath e x p).symm.map e.invFun.continuous).trans
        ((p.map e.invFun.continuous).symm.trans (e.left_inv.some.evalAt x))).toContinuousMap.toFun t := rfl

/-- Every ACTUAL corrected inverse root time is its SAME original defect-map/raw-root word. -/
theorem originalCorrectedInverseWeakMap_rootPath_apply (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) (t : unitInterval) :
    (originalCorrectedInverseWeakMap e x p).rootPath.toContinuousMap.toFun t =
      (((originalInverseDefectPath e x p).symm.map e.invFun.continuous).trans
        ((p.map e.invFun.continuous).symm.trans (e.left_inv.some.evalAt x))).toContinuousMap.toFun t :=
  originalCorrectedInverseRootValueComputed e x p t

private theorem originalCorrectedInverseHomValueComputed (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) : (originalCorrectedInverseWeakMap e x p).hom = e.invFun := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- WHOLE actual corrected inverse real map is the SAME original inverse map. -/
theorem originalCorrectedInverseWeakMap_hom (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) : (originalCorrectedInverseWeakMap e x p).hom = e.invFun :=
  originalCorrectedInverseHomValueComputed e x p

end ContinuousMap.HomotopyEquiv

end

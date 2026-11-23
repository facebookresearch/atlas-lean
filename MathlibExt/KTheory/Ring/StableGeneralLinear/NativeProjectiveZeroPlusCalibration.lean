/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.ProjectiveZeroPlusTransport

/-!
# The native projective zero/plus comparison retains its original source

The original strict BGL-source triangle and both full inverse families
are transported through the same actual native zero Iso. Its original
model map and entire unit-retuning trace remain part of the result. The
forward source triangle is derived relative to the original BGL point.
-/

noncomputable section

open CategoryTheory Topology
open CategoryTheory.SInverseS.ComponentTranslation
open scoped ContinuousMap

universe u v w

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The Ring-only native family retains the same strict source triangle, both full families and unit
  trace. -/
public theorem nativeProjectiveZeroPlusCalibratedEquivalence_exists :
    let C := FGProjectiveCat.{max u v} R
    let Z := AlgebraicKTheory.RingK0.projectiveZeroSpace.{u, v, w} R
    let z := AlgebraicKTheory.RingK0.projectiveZeroPoint.{u, v, w} R
    let B := independentBGLCellTarget R
    let b := independentBGLCellPoint R
    let i := independentBGLCellInclusion R
    let X := zeroSpace (C := FGProjectiveCat.IdempotentModel R)
    let x := zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
    let Y := zeroSpace (C := C)
    let y := zeroSpacePoint (C := C)
    let I := nativeZeroRealizationIso.{(max u v) + 1, max u v, w} (C := C)
    ∃ d : X ≃ₕ Y, d.toFun x = y ∧ d.invFun y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (d.invFun.comp d.toFun) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (d.toFun.comp d.invFun) (ContinuousMap.id Y) {y}) ∧
      (∃ K : ContinuousMap.Homotopy
          (finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).toFun d.toFun,
        ∀ t : unitInterval, K (t, x) = finiteFreeRowProjectiveZeroUnitPath.{u, v} R t) ∧
      ∃ a : Z ≃ₕ B, a.toFun z = b ∧ a.invFun b = z ∧
        Nonempty (ContinuousMap.HomotopyRel (a.invFun.comp a.toFun) (ContinuousMap.id Z) {z}) ∧
        Nonempty (ContinuousMap.HomotopyRel (a.toFun.comp a.invFun) (ContinuousMap.id B) {b}) ∧
        a.invFun.comp i.hom = I.inv.hom.comp (d.toFun.comp (finiteFreeRowBasedZeroComparison R).hom)
            ∧
        Nonempty (ContinuousMap.HomotopyRel
          (a.toFun.comp (I.inv.hom.comp (d.toFun.comp (finiteFreeRowBasedZeroComparison R).hom)))
          i.hom {ordinaryBGLBasepoint R}) := by
  let C := FGProjectiveCat.{max u v} R
  let Z := AlgebraicKTheory.RingK0.projectiveZeroSpace.{u, v, w} R
  let z := AlgebraicKTheory.RingK0.projectiveZeroPoint.{u, v, w} R
  let B := independentBGLCellTarget R
  let b := independentBGLCellPoint R
  let i := independentBGLCellInclusion R
  let Y := zeroSpace (C := C)
  let y := zeroSpacePoint (C := C)
  obtain ⟨d, hd, hdi, ⟨DL⟩, ⟨DR⟩, hTrace, e0, hSource, he, hei, ⟨L0⟩, ⟨S0⟩⟩ :=
    finiteFreeRowIndependentPlusProjectiveZeroEquivalence_exists.{u, v} R
  let I := nativeZeroRealizationIso.{(max u v) + 1, max u v, w} (C := C)
  let h : Z ≃ₜ Y := TopCat.homeoOfIso I
  let e := h.toHomotopyEquiv.trans e0.symm
  have hz : h z = y := by
    change I.hom z = y
    exact (congrArg I.hom (AlgebraicKTheory.RingK0.projectiveZeroPoint_eq_native.{u, v, w} R)).trans
      (nativeZeroRealizationIso_point.{(max u v) + 1, max u v, w} (C := C))
  have hy : h.symm y = z := by
    change I.inv y = z
    exact (nativeZeroRealizationIso_inv_point.{(max u v) + 1, max u v, w} (C := C)).trans
      (AlgebraicKTheory.RingK0.projectiveZeroPoint_eq_native.{u, v, w} R).symm
  let hHom : C(Z, Y) := I.hom.hom
  let hInv : C(Y, Z) := I.inv.hom
  let LA := (S0.precomposePointRelative hHom z hz).compContinuousMap hInv
  let L : ContinuousMap.HomotopyRel
      (e.invFun.comp e.toFun) (ContinuousMap.id Z) {z} :=
    LA.cast (by apply ContinuousMap.ext; intro a; rfl)
      (by apply ContinuousMap.ext; intro a; exact h.symm_apply_apply a)
  let S : ContinuousMap.HomotopyRel
      (e.toFun.comp e.invFun) (ContinuousMap.id B) {b} :=
    L0.cast (by
      apply ContinuousMap.ext
      intro a
      change e0.invFun (e0.toFun a) = e0.invFun (h (h.symm (e0.toFun a)))
      exact (congrArg e0.invFun (h.apply_symm_apply (e0.toFun a))).symm) rfl
  have hez : e.toFun z = b := (congrArg e0.invFun hz).trans hei
  have heb : e.invFun b = z := (congrArg h.symm he).trans hy
  have hInverseSource : e.invFun.comp i.hom =
      hInv.comp (d.toFun.comp (finiteFreeRowBasedZeroComparison R).hom) := by
    change hInv.comp (e0.toFun.comp i.hom) =
      hInv.comp (d.toFun.comp (finiteFreeRowBasedZeroComparison R).hom)
    exact congrArg (fun f => hInv.comp f) hSource
  let T := S.precomposePointRelative i.hom (ordinaryBGLBasepoint R)
    (independentBGLCellInclusion_point R)
  let HSource : ContinuousMap.HomotopyRel
      (e.toFun.comp (hInv.comp (d.toFun.comp (finiteFreeRowBasedZeroComparison R).hom)))
      i.hom {ordinaryBGLBasepoint R} :=
    T.cast (by
      apply ContinuousMap.ext
      intro a
      exact congrArg e.toFun (congrArg (fun f => f a) hInverseSource))
      (by apply ContinuousMap.ext; intro a; rfl)
  exact ⟨d, hd, hdi, ⟨DL⟩, ⟨DR⟩, hTrace,
    e, hez, heb, ⟨L⟩, ⟨S⟩, hInverseSource, ⟨HSource⟩⟩

end AlgebraicKTheory.StableGL

end

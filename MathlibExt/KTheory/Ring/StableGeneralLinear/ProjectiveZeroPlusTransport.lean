/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowProjectivePlusEquivalence
public import MathlibExt.KTheory.Ring.K0.ComponentProduct

/-!
# The original native projective zero and the actual independent cell plus

The canonical native/ordinary zero realization homeomorphism composes
with the inverse of the derived full-projective plus equivalence. Its
actual forward and inverse point equations transport both complete
singleton-relative inverse families to the original native zero point.
The Ring and independent projective/native universes are unchanged.
-/

noncomputable section

open CategoryTheory Topology
open CategoryTheory.SInverseS.ComponentTranslation
open scoped ContinuousMap

universe u v w

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The ORIGINAL native full-projective zero space is based homotopy
equivalent to the SAME independently constructed cell plus. Both original
point-relative inverse families are derived without any model or comparison
input, and all projective/native carrier parameters remain independent. -/
public theorem nativeProjectiveZeroPlusEquivalence_exists :
    let Z := AlgebraicKTheory.RingK0.projectiveZeroSpace.{u, v, w} R
    let z := AlgebraicKTheory.RingK0.projectiveZeroPoint.{u, v, w} R
    let B := independentBGLCellTarget R
    let b := independentBGLCellPoint R
    ∃ e : Z ≃ₕ B, e.toFun z = b ∧ e.invFun b = z ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id Z) {z}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id B) {b}) := by
  let C := FGProjectiveCat.{max u v} R
  let Z := AlgebraicKTheory.RingK0.projectiveZeroSpace.{u, v, w} R
  let z := AlgebraicKTheory.RingK0.projectiveZeroPoint.{u, v, w} R
  let B := independentBGLCellTarget R
  let b := independentBGLCellPoint R
  let Y := zeroSpace (C := C)
  let y := zeroSpacePoint (C := C)
  obtain ⟨_d, _, _, _, _, _, e₀, _, he, hei, ⟨L₀⟩, ⟨S₀⟩⟩ :=
    finiteFreeRowIndependentPlusProjectiveZeroEquivalence_exists.{u, v} R
  let I := nativeZeroRealizationIso.{(max u v) + 1, max u v, w} (C := C)
  let h : Z ≃ₜ Y := TopCat.homeoOfIso I
  let e := h.toHomotopyEquiv.trans e₀.symm
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
  let LA := (S₀.precomposePointRelative hHom z hz).compContinuousMap hInv
  let L : ContinuousMap.HomotopyRel
      (e.invFun.comp e.toFun) (ContinuousMap.id Z) {z} :=
    LA.cast (by apply ContinuousMap.ext; intro a; rfl)
      (by apply ContinuousMap.ext; intro a; exact h.symm_apply_apply a)
  let S : ContinuousMap.HomotopyRel
      (e.toFun.comp e.invFun) (ContinuousMap.id B) {b} :=
    L₀.cast (by
      apply ContinuousMap.ext
      intro a
      change e₀.invFun (e₀.toFun a) = e₀.invFun (h (h.symm (e₀.toFun a)))
      exact (congrArg e₀.invFun (h.apply_symm_apply (e₀.toFun a))).symm) rfl
  have hez : e.toFun z = b := (congrArg e₀.invFun hz).trans hei
  have heb : e.invFun b = z := (congrArg h.symm he).trans hy
  exact ⟨e, hez, heb, ⟨L⟩, ⟨S⟩⟩

end AlgebraicKTheory.StableGL

end

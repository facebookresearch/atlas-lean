/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowPlusZeroEquivalence
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowProjectiveZeroBased
public import MathlibExt.Topology.Homotopy.PointRelativeComposition

/-!
# The original independent cell plus and the full projective zero model

The derived small-row plus equivalence composes with the original based
small/full-projective model transport. The Ring is unchanged and the
projective carrier is independent. Both complete inverse families are
composed through their actual point equations. The original model-retuning
homotopy and its entire zero-unit trace remain part of the result, together
with the literal composite source triangle. No comparison, model, inverse
or family is supplied by the caller.
-/

noncomputable section

open CategoryTheory Topology
open scoped ContinuousMap

universe u v

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The SAME independent cell plus is based homotopy equivalent to the
ORIGINAL full-projective zero space in independent carrier universes.
The actual derived model map, both model inverse families and entire
original unit-retuning trace are retained. Both plus inverse families
fix the original points and the source triangle uses that SAME model map. -/
public theorem finiteFreeRowIndependentPlusProjectiveZeroEquivalence_exists :
    let B := independentBGLCellTarget R
    let i := independentBGLCellInclusion R
    let b := independentBGLCellPoint R
    let X := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)
    let x := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
    let Y := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)
    let y := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max u v} R)
    ∃ d : X ≃ₕ Y, d.toFun x = y ∧ d.invFun y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (d.invFun.comp d.toFun) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (d.toFun.comp d.invFun) (ContinuousMap.id Y) {y}) ∧
      (∃ K : ContinuousMap.Homotopy
          (finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).toFun d.toFun,
        ∀ t : unitInterval, K (t, x) = finiteFreeRowProjectiveZeroUnitPath.{u, v} R t) ∧
      ∃ e : B ≃ₕ Y,
        e.toFun.comp i.hom = d.toFun.comp (finiteFreeRowBasedZeroComparison R).hom ∧
        e.toFun b = y ∧ e.invFun y = b ∧
        Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id B) {b}) ∧
        Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) := by
  let B := independentBGLCellTarget R
  let i := independentBGLCellInclusion R
  let b := independentBGLCellPoint R
  let X := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)
  let x := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
  let Y := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)
  let y := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max u v} R)
  obtain ⟨d, hd, hdi, ⟨DL⟩, ⟨DR⟩, hTrace⟩ :=
    finiteFreeRowProjectiveZeroBasedEquivalence_exists.{u, v} R
  obtain ⟨e₀, hSource, he, hei, ⟨EL⟩, ⟨ER⟩, _⟩ :=
    finiteFreeRowIndependentPlusZeroEquivalence_exists R
  let e := e₀.trans d
  let L : ContinuousMap.HomotopyRel
      (e.invFun.comp e.toFun) (ContinuousMap.id B) {b} :=
    e₀.transLeftHomotopyRel d b x he EL DL
  let S : ContinuousMap.HomotopyRel
      (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y} :=
    e₀.transRightHomotopyRel d x y hdi ER DR
  have hCompositeSource : e.toFun.comp i.hom =
      d.toFun.comp (finiteFreeRowBasedZeroComparison R).hom := by
    change d.toFun.comp (e₀.toFun.comp i.hom) = _
    exact congrArg (fun k => d.toFun.comp k) hSource
  have hCompositePoint : e.toFun b = y := (congrArg d.toFun he).trans hd
  have hCompositeInversePoint : e.invFun y = b := (congrArg e₀.invFun hdi).trans hei
  exact ⟨d, hd, hdi, ⟨DL⟩, ⟨DR⟩, hTrace,
    e, hCompositeSource, hCompositePoint, hCompositeInversePoint, ⟨L⟩, ⟨S⟩⟩

end AlgebraicKTheory.StableGL

end

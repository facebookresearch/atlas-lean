/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowPlusZeroEquivalence
import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowProjectivePlusEquivalence

noncomputable section

open CategoryTheory Topology
open scoped ContinuousMap

universe u v

namespace AlgebraicKTheory.StableGL

example (R : Type u) [Ring R] :
    let B := independentBGLCellTarget R
    let i := independentBGLCellInclusion R
    let b := independentBGLCellPoint R
    let Y := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)
    let y := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
    ∃ e : B ≃ₕ Y,
      e.toFun.comp i.hom = (finiteFreeRowBasedZeroComparison R).hom ∧
      e.toFun b = y ∧ e.invFun y = b ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id B) {b}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) := by
  obtain ⟨e, hSource, he, hei, L, S, _⟩ :=
    finiteFreeRowIndependentPlusZeroEquivalence_exists R
  exact ⟨e, hSource, he, hei, L, S⟩

example (R : Type u) [Ring R] :
    let B := independentBGLCellTarget R
    let i := independentBGLCellInclusion R
    let Y := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)
    ∃ e : B ≃ₕ Y,
      ∀ G : B ⟶ Y, i ≫ G = finiteFreeRowBasedZeroComparison R →
        Nonempty (ContinuousMap.HomotopyRel e.toFun G.hom (Set.range i)) ∧
          Nonempty (ContinuousMap.HomotopyRel G.hom e.toFun (Set.range i)) := by
  obtain ⟨e, _, _, _, _, _, hUnique⟩ := finiteFreeRowIndependentPlusZeroEquivalence_exists R
  exact ⟨e, hUnique⟩

example (R : Type u) [Ring R] :
    let B := independentBGLCellTarget R
    let b := independentBGLCellPoint R
    let Y := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)
    let y := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max u v} R)
    ∃ e : B ≃ₕ Y, e.toFun b = y ∧ e.invFun y = b ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id B) {b}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) := by
  obtain ⟨_d, _, _, _, _, _, e, _, he, hei, L, S⟩ :=
    finiteFreeRowIndependentPlusProjectiveZeroEquivalence_exists.{u, v} R
  exact ⟨e, he, hei, L, S⟩

end AlgebraicKTheory.StableGL

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowProjectiveZeroBased

noncomputable section

open CategoryTheory AlgebraicKTheory.StableGL

universe u v

variable (R : Type u) [Ring R]

example :
    let X := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)
    let Y := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)
    let x := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
    let y := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max u v} R)
    ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun x = y ∧ e.invFun y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) := by
  obtain ⟨e, hf, hg, hL, hR, K, hK⟩ :=
    finiteFreeRowProjectiveZeroBasedEquivalence_exists.{u, v} R
  exact ⟨e, hf, hg, hL, hR⟩

example :
    let X := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)
    let Y := SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)
    let x := SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
    ∃ e : ContinuousMap.HomotopyEquiv X Y, ∃ K : ContinuousMap.Homotopy
        (finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).toFun e.toFun,
      ∀ t : unitInterval, K (t, x) = finiteFreeRowProjectiveZeroUnitPath.{u, v} R t := by
  obtain ⟨e, hf, hg, hL, hR, K, hK⟩ :=
    finiteFreeRowProjectiveZeroBasedEquivalence_exists.{u, v} R
  exact ⟨e, K, hK⟩

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowPlusComparison

noncomputable section

open CategoryTheory AlgebraicTopology
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R]

example (p : FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R))
    (hp : p ∈ BGLPlusSubgroup R) :
    FundamentalGroup.mapOfEq (finiteFreeRowBasedZeroComparison R).hom rfl p = 1 :=
  finiteFreeRowBasedZeroComparison_kills_stableElementary R p hp

example :
    let X := ordinaryBGL R
    let x := ordinaryBGLBasepoint R
    let P := BGLPlusSubgroup R
    letI : (classifyingNerve R).IsConnected :=
      CategoryTheory.nerve_isConnected_of_category_isConnected
    letI : PathConnectedSpace X :=
      SSet.pathConnectedSpace_realization_of_isConnected (classifyingNerve R)
    let B := LoopCellRegularThreeComparison.originalThree X x P
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    ∃ F : B ⟶ SInverseS.ComponentTranslation.zeroSpace
        (C := FGProjectiveCat.IdempotentModel R),
      i ≫ F = finiteFreeRowBasedZeroComparison R ∧
      F (i x) = SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.IdempotentModel R) ∧
      (∀ q : ℕ, IsIso ((singularIntegralHomologyFunctor q).map F)) := by
  letI : (classifyingNerve R).IsConnected :=
    CategoryTheory.nerve_isConnected_of_category_isConnected
  obtain ⟨F, hF, hPoint, hH, hUnique⟩ := finiteFreeRowIndependentPlusComparison_exists R
  exact ⟨F, hF, hPoint, hH⟩

example :
    let X := ordinaryBGL R
    let x := ordinaryBGLBasepoint R
    let P := BGLPlusSubgroup R
    letI : (classifyingNerve R).IsConnected :=
      CategoryTheory.nerve_isConnected_of_category_isConnected
    letI : PathConnectedSpace X :=
      SSet.pathConnectedSpace_realization_of_isConnected (classifyingNerve R)
    let B := LoopCellRegularThreeComparison.originalThree X x P
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    let Y := SInverseS.ComponentTranslation.zeroSpace
      (C := FGProjectiveCat.IdempotentModel R)
    ∃ F : B ⟶ Y, i ≫ F = finiteFreeRowBasedZeroComparison R ∧
      ∀ G : B ⟶ Y, i ≫ G = finiteFreeRowBasedZeroComparison R →
        Nonempty (ContinuousMap.HomotopyRel F.hom G.hom (Set.range i)) ∧
          Nonempty (ContinuousMap.HomotopyRel G.hom F.hom (Set.range i)) := by
  letI : (classifyingNerve R).IsConnected :=
    CategoryTheory.nerve_isConnected_of_category_isConnected
  obtain ⟨F, hF, hPoint, hH, hUnique⟩ := finiteFreeRowIndependentPlusComparison_exists R
  exact ⟨F, hF, hUnique⟩

end

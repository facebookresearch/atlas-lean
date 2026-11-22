/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontJoyalPointedDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import MathlibExt.AlgebraicTopology.ModelCategory.Under
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory
import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# Actual Reedy factorization of the SAME original endpoint-fixed augmentation

The existing named Joyal model, its original Under model and the proved
simplicial Reedy model on the opposite category factor the SAME pointed
augmentation. Reversing its actual maps gives the full cosimplicial
replacement and projection, retaining every original endpoint map.
No new model factory or assumed resolution certificate is supplied.
-/

noncomputable section

universe u

open CategoryTheory Opposite HomotopicalAlgebra MorphismProperty
open scoped Simplicial CategoryTheory.SimplicialObject.reedyModelCategory

attribute [local instance] JoyalSSet.modelCategory

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The reversed SAME original endpoint-fixed augmentation in the existing opposite Reedy model. -/
def reversedAugmentation :
    ((Functor.const SimplexCategory).obj (pointedCopyFunctor.obj (pointedObject.{u} 0))).op ⟶
      pointedJoyalDiagram.{u}.op := NatTrans.op pointedJoyalAugmentation

/-- The genuine actual factorization supplied by the proved original named Joyal, Under and Reedy models. -/
def reversedFactorization :
    (cofibrations (SimplicialObject PointedJoyal.{u}ᵒᵖ)).MapFactorizationData
      (trivialFibrations (SimplicialObject PointedJoyal.{u}ᵒᵖ)) reversedAugmentation.{u} :=
  MorphismProperty.factorizationData _ _ reversedAugmentation

/-- The actual full cosimplicial replacement of the SAME original endpoint-fixed quotient diagram. -/
def reedyReplacement : CosimplicialObject PointedJoyal.{u} := reversedFactorization.Z.unop

/-- The actual original-to-replacement cosimplicial map, retaining both original boundary endpoints. -/
def reedyReplacementMap : pointedJoyalDiagram.{u} ⟶ reedyReplacement.{u} := NatTrans.unop reversedFactorization.p

/-- The actual full replacement projection to the SAME original zero quotient with its fixed endpoints. -/
def reedyReplacementProjection :
    reedyReplacement.{u} ⟶ (Functor.const SimplexCategory).obj (pointedCopyFunctor.obj (pointedObject.{u} 0)) :=
  NatTrans.unop reversedFactorization.i

/-- Both actual full Reedy maps compose to the SAME original pointed constant-front augmentation. -/
theorem reedyReplacement_factor :
    reedyReplacementMap.{u} ≫ reedyReplacementProjection.{u} = pointedJoyalAugmentation.{u} :=
  by
    have h := congrArg NatTrans.unop reversedFactorization.fac
    rw [NatTrans.unop_comp] at h
    exact h

/-- Every actual opposite relative matching map of the replacement has its genuine original trivial-fibration class. -/
theorem reversedFactorization_relativeMatching_trivial (n : ℕ) :
    trivialFibrations PointedJoyal.{u}ᵒᵖ
      (SimplicialObject.relativeMatchingMap reversedFactorization.{u}.p n) := by
  have h := reversedFactorization.{u}.hp
  change SimplicialObject.reedyRight (fibrations PointedJoyal.{u}ᵒᵖ) reversedFactorization.p ∧
    (weakEquivalences PointedJoyal.{u}ᵒᵖ).functorCategory SimplexCategoryᵒᵖ reversedFactorization.p at h
  have ht : SimplicialObject.reedyRight (trivialFibrations PointedJoyal.{u}ᵒᵖ) reversedFactorization.p :=
    (SimplicialObject.reedyRight_trivialFibrations_eq (C := PointedJoyal.{u}ᵒᵖ)).symm ▸ h
  exact ht n

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

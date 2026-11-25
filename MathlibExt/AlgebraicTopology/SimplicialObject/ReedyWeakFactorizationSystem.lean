/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyLifting
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyFactorization
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# Reedy weak factorization systems for simplicial objects

A weak factorization system on the base category induces the corresponding degreewise Reedy weak
factorization system. This file does not choose weak equivalences or install a model structure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]

/-- A weak factorization system on the base category induces the corresponding Reedy weak
factorization system on simplicial objects. -/
noncomputable instance reedyIsWeakFactorizationSystem
    (P Q : MorphismProperty C) [P.IsWeakFactorizationSystem Q] :
    (reedyLeft P).IsWeakFactorizationSystem (reedyRight Q) := by
  let _ : P.IsStableUnderRetracts := by
    rw [← llp_eq_of_wfs P Q]
    infer_instance
  let _ : Q.IsStableUnderRetracts := by
    rw [← rlp_eq_of_wfs P Q]
    infer_instance
  have hPQ : P ≤ Q.llp := by
    rw [llp_eq_of_wfs P Q]
  exact IsWeakFactorizationSystem.mk' (reedyLeft P) (reedyRight Q)
    (fun i p hi hp => reedyLeft_le_llp_reedyRight P Q hPQ i hi p hp)

end CategoryTheory.SimplicialObject

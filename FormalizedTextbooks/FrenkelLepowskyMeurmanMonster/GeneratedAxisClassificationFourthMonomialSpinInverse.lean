/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinPermutation

/-! Exact inverse matrices for the four original monomial spin-label pullbacks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Literal inverse row masks, verified against the original final spin models. -/
def generatedFourthMonomialInverseRows : Fin 4 → Fin 12 → Fin 4096 :=
  ![
    ![1089, 1090, 946, 1096, 16, 241, 145, 1041, 1629, 1771, 1233, 2919],
    ![1073, 2, 1752, 1508, 1056, 1040, 128, 64, 1536, 1280, 1024, 3840],
    ![1, 527, 2034, 1362, 177, 32, 97, 128, 1654, 172, 1185, 2048],
    ![1073, 1362, 4, 1896, 1040, 1056, 64, 128, 1280, 512, 1024, 3584]
  ]

/-- The inverse binary matrix of each original signed model. -/
def generatedFourthMonomialInverseMatrix (k : Fin 4) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  (representativeSpinRowsModel (generatedFourthMonomialInverseRows k) 0).coordinate

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check four pairs of12 by12 inverse matrices, without enumerating spin vectors.
/-- Both inverse identities hold for the literal original spin-label matrices. -/
theorem generatedFourth_monomial_inverse_matrices : ∀ k : Fin 4,
    (generatedFourthMonomialSpinModel k).coordinate * generatedFourthMonomialInverseMatrix k = 1 ∧
    generatedFourthMonomialInverseMatrix k *
      (generatedFourthMonomialSpinModel k).coordinate = 1 := by
  decide +kernel

/-- The actual final matrix pullback is an explicit binary linear equivalence. -/
def generatedFourthMonomialLabelEquiv (k : Fin 4) : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun := (generatedFourthMonomialSpinModel k).coordinate.mulVec
  invFun := (generatedFourthMonomialInverseMatrix k).mulVec
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _
  left_inv t := by
    rw [Matrix.mulVec_mulVec, (generatedFourth_monomial_inverse_matrices k).2,
      Matrix.one_mulVec]
  right_inv t := by
    rw [Matrix.mulVec_mulVec, (generatedFourth_monomial_inverse_matrices k).1,
      Matrix.one_mulVec]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

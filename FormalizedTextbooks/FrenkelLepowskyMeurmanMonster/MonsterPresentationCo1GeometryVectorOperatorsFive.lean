/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The certificate operator alphabet retains the exact five actual Conway generators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTransportMatrices

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The five original actual generators have these positions in the fifteen-operator alphabet. -/
def monsterCo1GeometryVectorFiveOperator : Fin 5 → Fin 15 := ![0, 5, 6, 13, 14]

/-- Complete actual operator matrices coincide with the independently checked original five. -/
theorem monsterCo1GeometryVectorFiveOperator_matrix (k : Fin 5) :
    monsterCo1GeometryTransportOperatorMatrix (monsterCo1GeometryVectorFiveOperator k) =
      omegaOrbitBinaryMatrices k := by
  have hc : ∀ k : Fin 5,
      monsterCo1GeometryTransportOperatorMatrix (monsterCo1GeometryVectorFiveOperator k) =
        omegaOrbitBinaryMatrices k := by decide +kernel
  exact hc k

/-- Faithfulness binds the complete physical operator alphabet to the exact actual generators. -/
theorem monsterCo1GeometryVectorFiveOperator_actual (k : Fin 5) :
    monsterCo1GeometryTransportOperator (monsterCo1GeometryVectorFiveOperator k) =
      monsterCo1FiveGenerator k := by
  apply co1BinaryAction_injective
  apply LinearEquiv.ext
  intro v
  rw [monsterCo1GeometryTransportOperator_binary,
    monsterCo1GeometryVectorFiveOperator_matrix]
  change omegaOrbitBinaryMatrices k *ᵥ v = leechBinaryAction (omegaOrbitIsometry k) v
  exact (omegaOrbitIsometry_binary k v).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

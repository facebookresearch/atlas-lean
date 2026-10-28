/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The compact mask product is tested on a noncommuting pair of actual Conway operators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskOperators

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Complete binary matrix of actual Xi times the sign of encoder basis vector four. -/
def monsterCo1GeometryBinaryXiSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Exact row masks of the same complete actual product matrix. -/
def monsterCo1GeometryBinaryXiSignMasks : Fin 24 → ℕ :=
    ![8445984, 8442528, 8434144, 8418144, 8388624, 32, 64, 128, 256, 512, 8388608, 4194304,
    8392750, 8397485, 8405483, 8422247, 65536, 131087, 262668, 525062, 1048716, 2097354,
    4261903, 8389632]

/-- The compact XOR product certifies the original actual matrix product in this order. -/
theorem monsterCo1GeometryBinaryXiSign_product :
    monsterCo1GeometryTransportOperatorMatrix 0 * monsterCo1GeometryTransportOperatorMatrix 5 =
      monsterCo1GeometryBinaryXiSignMatrix := by
  exact monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    (monsterCo1GeometryBinaryOperatorMasks 0) (monsterCo1GeometryBinaryOperatorMasks 5)
    monsterCo1GeometryBinaryXiSignMasks (monsterCo1GeometryBinaryOperatorMasks_decode 0)
    (monsterCo1GeometryBinaryOperatorMasks_decode 5) (by decide +kernel) (by decide +kernel)

/-- This is the complete binary action of the literal actual Conway class product. -/
theorem monsterCo1GeometryBinaryXiSign_actual (v : Fin 24 → ZMod 2) :
    co1BinaryAction (monsterCo1GeometryTransportOperator 0 *
      monsterCo1GeometryTransportOperator 5) v = monsterCo1GeometryBinaryXiSignMatrix *ᵥ v :=
  monsterCo1GeometryTransport_matrix_mul _ _ _ _ _
    (monsterCo1GeometryTransportOperator_binary 0) (monsterCo1GeometryTransportOperator_binary 5)
    monsterCo1GeometryBinaryXiSign_product v

/-- Reversing the actual operator order changes this matrix, testing the decoder orientation. -/
theorem monsterCo1GeometryBinaryXiSign_not_reverse :
    monsterCo1GeometryBinaryXiSignMatrix ≠
    monsterCo1GeometryTransportOperatorMatrix 5 * monsterCo1GeometryTransportOperatorMatrix 0
    := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 24) (Fin 24) (ZMod 2) => A 0 5) h
  have hn : monsterCo1GeometryBinaryXiSignMatrix 0 5 ≠
      (monsterCo1GeometryTransportOperatorMatrix 5 * monsterCo1GeometryTransportOperatorMatrix 0)
        0 5 := by decide +kernel
  exact hn he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

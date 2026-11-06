/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortMatrixData

/-! Sparse evaluation of the unchanged actual extraspecial central polynomial. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Literal central coefficients, with the bit extraction already evaluated. -/
def generatedFourthLiftQPhaseLiteral : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Each of the 576 literal phase coefficients equals the certified binary row data. -/
theorem generatedFourth_lift_q_phase_literal :
    generatedFourthLiftQPhaseMatrix = generatedFourthLiftQPhaseLiteral := by
  decide +kernel

/-- The complete literal central polynomial, evaluated only at its nonzero coefficients. -/
def generatedFourthLiftQPhaseFast (v : Fin 24 → ZMod 2) : ZMod 2 :=
  v 0 * v 0 +
    v 0 * v 12 +
    v 1 * v 13 +
    v 2 * v 2 +
    v 2 * v 10 +
    v 2 * v 14 +
    v 2 * v 23 +
    v 3 * v 3 +
    v 3 * v 10 +
    v 3 * v 15 +
    v 3 * v 23 +
    v 4 * v 5 +
    v 4 * v 7 +
    v 5 * v 5 +
    v 5 * v 6 +
    v 5 * v 9 +
    v 5 * v 12 +
    v 5 * v 13 +
    v 5 * v 14 +
    v 5 * v 15 +
    v 6 * v 6 +
    v 6 * v 14 +
    v 6 * v 15 +
    v 7 * v 7 +
    v 7 * v 9 +
    v 7 * v 13 +
    v 7 * v 14 +
    v 8 * v 8 +
    v 8 * v 9 +
    v 8 * v 14 +
    v 8 * v 15 +
    v 9 * v 9 +
    v 9 * v 10 +
    v 9 * v 13 +
    v 9 * v 15 +
    v 9 * v 23 +
    v 10 * v 16 +
    v 10 * v 18 +
    v 10 * v 22 +
    v 11 * v 23 +
    v 12 * v 12 +
    v 12 * v 13 +
    v 12 * v 14 +
    v 12 * v 15 +
    v 12 * v 23 +
    v 13 * v 13 +
    v 13 * v 14 +
    v 13 * v 15 +
    v 14 * v 15 +
    v 14 * v 23 +
    v 15 * v 15 +
    v 15 * v 23 +
    v 16 * v 16 +
    v 16 * v 23 +
    v 18 * v 23 +
    v 22 * v 22 +
    v 22 * v 23 +
    v 23 * v 23

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Expand the 576 constant matrix coefficients before collecting its 58 nonzero monomials.
/-- Sparse evaluation retains every diagonal and off-diagonal central bit. -/
theorem generatedFourth_lift_q_phase_fast (v : Fin 24 → ZMod 2) :
    generatedFourthLiftQMatrixPhase generatedFourthLiftQPhaseMatrix v =
      generatedFourthLiftQPhaseFast v := by
  unfold generatedFourthLiftQMatrixPhase
  rw [generatedFourth_lift_q_phase_literal]
  simp [Matrix.toBilin'_apply, generatedFourthLiftQPhaseLiteral,
    generatedFourthLiftQPhaseFast, Fin.sum_univ_succ]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

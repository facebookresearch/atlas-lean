/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagSpinData

/-! Sparse evaluation retains every actual Parker phase of the correction spin operator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Literal coefficient matrix of the entire correction quadratic phase. -/
def generatedFourthLiftPPhaseMatrix : Fin 12 → Fin 12 → ZMod 2 :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Each sparse coefficient is checked against the original Parker matrix. -/
theorem generatedFourth_lift_p_phase_matrix :
    generatedFourthFlagLiftPhase = generatedFourthLiftPPhaseMatrix := by decide +kernel

/-- The original correction phase evaluated at its nonzero monomials only. -/
def generatedFourthLiftPPhaseFast (t : SpinIndex) : ZMod 2 :=
  t 0 * t 5 +
    t 0 * t 10 +
    t 1 * t 5 +
    t 1 * t 7 +
    t 1 * t 9 +
    t 1 * t 10 +
    t 2 * t 5 +
    t 2 * t 6 +
    t 2 * t 7 +
    t 2 * t 8 +
    t 2 * t 10 +
    t 3 * t 5 +
    t 3 * t 6 +
    t 3 * t 8 +
    t 3 * t 9 +
    t 3 * t 10 +
    t 6 * t 7 +
    t 8 * t 9

/-- This sparse polynomial is the unchanged full actual correction phase. -/
theorem generatedFourth_lift_p_phase_fast (t : SpinIndex) :
    monsterMonomialQuadratic generatedFourthFlagLiftPhase t =
      generatedFourthLiftPPhaseFast t := by
  rw [generatedFourth_lift_p_phase_matrix]
  simp [monsterMonomialQuadratic, generatedFourthLiftPPhaseMatrix,
    generatedFourthLiftPPhaseFast, Fin.sum_univ_succ]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

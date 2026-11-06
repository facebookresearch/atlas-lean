/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftYCoordinate

/-! Sparse polynomial evaluation of the unchanged genuine y82 quadratic phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Literal coefficient matrix of the original y82 phase polynomial. -/
def generatedFourthLiftYPhaseMatrix : Fin 12 → Fin 12 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0],
    ![0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]]

/-- Every coefficient of this matrix agrees with the genuine Parker/Fourier formula. -/
theorem generatedFourth_lift_y_phase_matrix :
    monsterSourceYPhaseMatrix monsterSourceY82Code = generatedFourthLiftYPhaseMatrix := by
  decide +kernel

/-- The original quadratic phase evaluated only at its nonzero monomials. -/
def generatedFourthLiftYPhaseFast (t : SpinIndex) : ZMod 2 :=
  t 0 * t 0 +
    t 0 * t 5 +
    t 0 * t 10 +
    t 2 * t 2 +
    t 2 * t 4 +
    t 2 * t 5 +
    t 2 * t 6 +
    t 2 * t 9 +
    t 2 * t 10 +
    t 3 * t 3 +
    t 3 * t 4 +
    t 3 * t 6 +
    t 3 * t 7 +
    t 3 * t 9 +
    t 3 * t 10 +
    t 4 * t 4 +
    t 4 * t 5 +
    t 4 * t 7 +
    t 5 * t 5 +
    t 5 * t 6 +
    t 5 * t 9 +
    t 6 * t 6 +
    t 6 * t 7 +
    t 7 * t 7 +
    t 7 * t 9 +
    t 11 * t 9

/-- Sparse evaluation retains the entire actual y82 phase exactly. -/
theorem generatedFourth_lift_y_phase_fast (t : SpinIndex) :
    generatedFourthLiftYPhase t = generatedFourthLiftYPhaseFast t := by
  rw [show generatedFourthLiftYPhase t =
      monsterMonomialQuadratic (monsterSourceYPhaseMatrix monsterSourceY82Code) t from
        (monsterSourceYPhaseMatrix_apply _ _).symm,
    generatedFourth_lift_y_phase_matrix]
  simp [monsterMonomialQuadratic, generatedFourthLiftYPhaseMatrix,
    generatedFourthLiftYPhaseFast, Fin.sum_univ_succ]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

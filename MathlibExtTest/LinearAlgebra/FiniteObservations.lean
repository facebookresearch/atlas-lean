/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.LinearAlgebra.FiniteObservations
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.IntervalCases

-- Different nonempty state spaces can give the same nonconstant output.
-- Checking times 0, 1, and 2 suffices for dimensions 1 and 2.
example : ∀ n : ℕ,
    Matrix.observation (!![2] : Matrix (Fin 1) (Fin 1) ℚ) ![1] ![1] n =
      Matrix.observation (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ)
        ![1, 1] ![1, 0] n := by
  apply (Matrix.observation_prefix_iff_all _ _ _ _ _ _).mp
  intro n hn
  interval_cases n <;>
    norm_num [Matrix.observation, pow_succ, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

-- Empty state spaces must require no observations.
example (A B : Matrix (Fin 0) (Fin 0) ℚ) (x c y d : Fin 0 → ℚ) :
    ∀ n : ℕ, dotProduct c ((A ^ n).mulVec x) =
      dotProduct d ((B ^ n).mulVec y) := by
  exact (Matrix.observation_prefix_iff_all A x c B y d).mp (by omega)

-- One matching observation need not distinguish two one-dimensional systems.
example : Matrix.observation (1 : Matrix (Fin 1) (Fin 1) ℚ) 1 1 0 =
    Matrix.observation (0 : Matrix (Fin 1) (Fin 1) ℚ) 1 1 0 := by
  simp [Matrix.observation]

example : Matrix.observation (1 : Matrix (Fin 1) (Fin 1) ℚ) 1 1 1 ≠
    Matrix.observation (0 : Matrix (Fin 1) (Fin 1) ℚ) 1 1 1 := by
  norm_num [Matrix.observation, dotProduct]

#print axioms Module.End.observation_zero_of_prefix
#print axioms Matrix.observation_prefix_iff_all

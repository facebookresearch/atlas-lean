/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.BooleanCubeMoments
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tests for the Boolean cube moment bounds
-/

namespace MathlibExtTest.Probability.BooleanCubeMoments

open MetaMathlibExt

/-- `sum_cubeVal_fourth_le` at `T = 1`. -/
example : ∑ σ : Fin 1 → Bool, (∑ t : Fin 1, BooleanCube.cubeVal (σ t)) ^ 4
    ≤ (2 : ℝ) ^ 1 * (3 * ((1 : ℕ) : ℝ) ^ 2) :=
  sum_cubeVal_fourth_le 1

/-- `moment_algebra` at `A = 4`, `B = 2`, `C = 4`, `M = 2`. -/
example : (2 : ℝ) ^ 3 ≤ (4 : ℝ) ^ 2 * 4 :=
  moment_algebra (4 : ℝ) (2 : ℝ) (4 : ℝ) (2 : ℝ) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- `khintchine_lower` at `T = 2`. -/
example : ∑ σ : Fin 2 → Bool, |∑ t : Fin 2, BooleanCube.cubeVal (σ t)|
    ≥ (2 : ℝ) ^ 2 * Real.sqrt (((2 : ℕ) : ℝ) / 3) :=
  khintchine_lower 2

-- Guarded axiom audit for the moment theorems.
/--
info: 'MetaMathlibExt.sum_cubeVal_fourth_le' depends on
 axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_cubeVal_fourth_le
/--
info: 'MetaMathlibExt.khintchine_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms khintchine_lower

end MathlibExtTest.Probability.BooleanCubeMoments

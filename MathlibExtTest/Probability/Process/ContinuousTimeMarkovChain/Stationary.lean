/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Stationary
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for stationarity and detailed balance

On the two-state rate matrix `!![-1, 1; 2, -2]`, the distribution `(2/3, 1/3)` is the
non-vacuity witness for `IsDetailedBalance`: it is in detailed balance, hence invariant for
the generator and for every `P t`, and the chain is reversible at every time. The uniform
distribution is a non-example: it is not invariant. Boundary cases: every vector is invariant
for the zero generator, and the zero vector satisfies the detailed-balance equations for every
matrix (so reversibility needs a probability vector).
-/

@[expose] public section

open Finset Matrix ProbabilityTheory

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.Stationary

/-- A two-state rate matrix: rate `1` from state `0` to `1`, rate `2` back. -/
def q2 : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 2, -2]

/-- Its stationary distribution `(2/3, 1/3)`. -/
noncomputable def π2 : Fin 2 → ℝ := ![2 / 3, 1 / 3]

theorem sum_row_q2 (i : Fin 2) : ∑ j, q2 i j = 0 := by
  fin_cases i <;> simp [q2, Fin.sum_univ_two]

-- Non-vacuity witness: `(2/3, 1/3)` is in detailed balance with `q2`.
theorem isDetailedBalance_π2 : IsDetailedBalance π2 q2 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [π2, q2]

-- Hence it is invariant for the generator and for every `P t`.
example : π2 ᵥ* q2 = 0 := isDetailedBalance_π2.vecMul_eq_zero sum_row_q2
example (t : ℝ) : π2 ᵥ* ctmcTransition q2 t = π2 :=
  isDetailedBalance_π2.vecMul_ctmcTransition sum_row_q2 t

-- Reversibility at time `t`: `π 0 P t 0 1 = π 1 P t 1 0`.
example (t : ℝ) : π2 0 * ctmcTransition q2 t 0 1 = π2 1 * ctmcTransition q2 t 1 0 :=
  isDetailedBalance_π2.ctmcTransition t 0 1

-- The predicate alone is algebraic: the zero vector, which is not a distribution, is in
-- detailed balance with every matrix.
example (Q : Matrix (Fin 2) (Fin 2) ℝ) : IsDetailedBalance 0 Q := by
  intro i j
  simp

-- The equivalence, used in the reverse direction.
example : π2 ᵥ* q2 = 0 :=
  (vecMul_eq_zero_iff_forall_vecMul_ctmcTransition π2 q2).mpr
    (isDetailedBalance_π2.vecMul_ctmcTransition sum_row_q2)

-- Non-example: the uniform distribution is not invariant for `q2`.
example : ¬ ∀ t, ![1 / 2, 1 / 2] ᵥ* ctmcTransition q2 t = ![(1 / 2 : ℝ), 1 / 2] := by
  rw [← vecMul_eq_zero_iff_forall_vecMul_ctmcTransition]
  intro h
  have := congrFun h 0
  norm_num [vecMul, dotProduct, q2, Fin.sum_univ_two] at this

-- Boundary case: every vector is invariant for the zero generator.
example (π : Fin 3 → ℝ) (t : ℝ) : π ᵥ* ctmcTransition 0 t = π :=
  (vecMul_eq_zero_iff_forall_vecMul_ctmcTransition π 0).mp (vecMul_zero π) t

#print axioms vecMul_eq_zero_iff_forall_vecMul_ctmcTransition
#print axioms IsDetailedBalance.ctmcTransition
#print axioms IsDetailedBalance.vecMul_ctmcTransition

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.Stationary

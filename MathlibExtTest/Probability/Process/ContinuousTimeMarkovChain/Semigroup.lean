/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Semigroup
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for the transition semigroup of a finite continuous-time Markov chain

On the two-state rate matrix `!![-1, 1; 2, -2]`: the identity at `t = 0`, the semigroup law
at concrete times, row sums at positive and negative times, nonnegativity, positivity and
row-stochasticity at positive times, time rescaling, uniformization at `c = 2`, and the
Kolmogorov equations at `t = 0` (the derivative is the generator). The first-order lower bound
`1 + t • A ≤ exp (t • A)` on a nonnegative matrix. Boundary cases: the zero generator gives the
constant chain, whose off-diagonal entries vanish (positivity needs positive off-diagonal
rates), and at `t = 0` the off-diagonal entries of `q2` vanish (positivity needs `t > 0`).
-/

@[expose] public section

open Finset Matrix ProbabilityTheory

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.Semigroup

/-- A two-state rate matrix: rate `1` from state `0` to `1`, rate `2` back. -/
def q2 : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 2, -2]

theorem isRateMatrix_q2 : IsRateMatrix q2 where
  nonneg_of_ne i j h := by fin_cases i <;> fin_cases j <;> simp_all [q2]
  sum_row i := by fin_cases i <;> simp [q2, Fin.sum_univ_two]

-- The identity at time `0`.
example : ctmcTransition q2 0 = 1 := ctmcTransition_zero q2

-- The semigroup law at concrete times.
example : ctmcTransition q2 3 = ctmcTransition q2 1 * ctmcTransition q2 2 := by
  rw [← ctmcTransition_add]; norm_num

-- Rows sum to `1` at positive and at negative times.
example : ∑ j, ctmcTransition q2 5 0 j = 1 := isRateMatrix_q2.sum_ctmcTransition 5 0
example : ∑ j, ctmcTransition q2 (-1) 1 j = 1 := isRateMatrix_q2.sum_ctmcTransition (-1) 1

-- Nonnegativity and row-stochasticity at positive times.
example (i j : Fin 2) : 0 ≤ ctmcTransition q2 1 i j :=
  isRateMatrix_q2.ctmcTransition_nonneg zero_le_one i j
example : ctmcTransition q2 (1 / 2) ∈ rowStochastic ℝ (Fin 2) :=
  isRateMatrix_q2.ctmcTransition_mem_rowStochastic (by norm_num)

-- Positivity at a positive time: both off-diagonal rates of `q2` are positive.
example (i j : Fin 2) : 0 < ctmcTransition q2 1 i j :=
  isRateMatrix_q2.ctmcTransition_pos
    (fun i j h => by fin_cases i <;> fin_cases j <;> simp_all [q2]) one_pos i j

-- Positivity needs `t > 0`: at `t = 0` the off-diagonal entry is `0`.
example : ctmcTransition q2 0 0 1 = 0 := by simp

-- The first-order lower bound on the nonnegative matrix `!![0, 1; 2, 0]` at `t = 1`.
example : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + 1 * !![(0 : ℝ), 1; 2, 0] 0 1 ≤
    ctmcTransition !![(0 : ℝ), 1; 2, 0] 1 0 1 :=
  one_add_le_ctmcTransition_of_nonneg
    (fun i j => by fin_cases i <;> fin_cases j <;> norm_num) zero_le_one 0 1

-- Doubling the rates doubles the speed.
example : ctmcTransition ((2 : ℝ) • q2) 1 = ctmcTransition q2 2 := by
  rw [ctmcTransition_smul]; norm_num

-- Uniformization at `c = 2`.
example (t : ℝ) : ctmcTransition q2 t =
    Real.exp (-(2 * t)) • ctmcTransition (q2 + (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t :=
  ctmcTransition_eq_exp_smul_uniformized q2 2 t

-- The generator commutes with the semigroup.
example (t : ℝ) : q2 * ctmcTransition q2 t = ctmcTransition q2 t * q2 :=
  (commute_ctmcTransition q2 t).eq

-- Kolmogorov equations at `t = 0`: the derivative is the generator.
example : HasDerivAt (ctmcTransition q2) q2 0 := by
  simpa using hasDerivAt_ctmcTransition_backward q2 0
example : HasDerivAt (ctmcTransition q2) q2 0 := by
  simpa using hasDerivAt_ctmcTransition_forward q2 0

-- Boundary case: the zero generator gives the constant chain.
example (t : ℝ) : ctmcTransition (0 : Matrix (Fin 3) (Fin 3) ℝ) t = 1 := by
  simp [ctmcTransition]

-- Positivity needs positive off-diagonal rates: under the zero generator the off-diagonal
-- entries stay `0` at every time.
example (t : ℝ) : ctmcTransition (0 : Matrix (Fin 3) (Fin 3) ℝ) t 0 1 = 0 := by
  simp [ctmcTransition]

#print axioms ctmcTransition_add
#print axioms hasDerivAt_ctmcTransition_backward
#print axioms hasDerivAt_ctmcTransition_forward
#print axioms IsRateMatrix.ctmcTransition_mem_rowStochastic
#print axioms IsRateMatrix.ctmcTransition_pos
#print axioms one_add_le_ctmcTransition_of_nonneg

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.Semigroup

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for finite continuous-time Markov chains as path processes

On the two-state rate matrix `!![-1, 1; 2, -2]`: the jump matrix, the probability law of the
steps (non-vacuity of the construction), a hand-computed path for a concrete step sequence,
and the main theorems instantiated. Boundary cases: the zero generator (every state absorbing,
infinite holding times, constant path) and a negative clock value (a null event under the
exponential law), which gives a zero holding time.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.Path

/-- A two-state rate matrix: rate `1` from state `0` to `1`, rate `2` back. -/
def q2 : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 2, -2]

theorem isRateMatrix_q2 : IsRateMatrix q2 where
  nonneg_of_ne i j h := by fin_cases i <;> fin_cases j <;> simp_all [q2]
  sum_row i := by fin_cases i <;> simp [q2, Fin.sum_univ_two]

theorem isRateMatrix_zero : IsRateMatrix (0 : Matrix (Fin 2) (Fin 2) ℝ) where
  nonneg_of_ne _ _ _ := le_rfl
  sum_row _ := by simp

-- The jump matrix of `q2` swaps the two states.
example : ctmcJumpMatrix q2 0 1 = 1 := by simp [ctmcJumpMatrix, q2]
example : ctmcJumpMatrix q2 0 0 = 0 := by simp [ctmcJumpMatrix, q2]
example : ctmcJumpMatrix q2 1 0 = 1 := by norm_num [ctmcJumpMatrix, q2]
example : ctmcJumpMatrix q2 ∈ rowStochastic ℝ (Fin 2) :=
  isRateMatrix_q2.ctmcJumpMatrix_mem_rowStochastic

-- Boundary: for the zero generator every state is absorbing.
example : ctmcJumpMatrix (0 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext i j; simp [ctmcJumpMatrix, Matrix.one_apply]

-- Non-vacuity: the step sequence has a probability law.
example : IsProbabilityMeasure (ctmcInputMeasure isRateMatrix_q2) := inferInstance
example : IsProbabilityMeasure (ctmcInputMeasure isRateMatrix_zero) := inferInstance

/-- A concrete step sequence: every random map swaps the states and every clock reads `1`. -/
def ωswap : ℕ → (Fin 2 → Fin 2) × ℝ := fun _ => (fun i => 1 - i, 1)

example : ctmcJumpChain 0 ωswap 1 = 1 := by decide
example : ctmcJumpChain 0 ωswap 2 = 0 := by decide

-- From state `0` (rate `1`) the first holding time is `1`; from state `1` (rate `2`) it is `1/2`.
example : ctmcHoldingTime q2 0 ωswap 0 = 1 := by
  simp [ctmcHoldingTime, ctmcJumpChain, ωswap, q2]
example : ctmcHoldingTime q2 0 ωswap 1 = ENNReal.ofReal (1 / 2) := by
  have : ctmcJumpChain 0 ωswap 1 = 1 := by decide
  simp [ctmcHoldingTime, this, ωswap, q2]

-- The path: `X 0 = 0`, and `X 1 = 1` since `T 1 = 1 ≤ 1 < 3 / 2 = T 2`.
example : ctmcPath q2 0 ωswap 0 = 0 := by
  have h : ctmcJumpTime q2 0 ωswap 1 = 1 := by
    simp [ctmcJumpTime, ctmcHoldingTime, ctmcJumpChain, ωswap, q2]
  exact ctmcPath_eq_of_mem (n := 0) 0 ωswap (by simp [ctmcJumpTime]) (by rw [h]; simp)

example : ctmcPath q2 0 ωswap 1 = 1 := by
  have h1 : ctmcJumpTime q2 0 ωswap 1 = 1 := by
    simp [ctmcJumpTime, ctmcHoldingTime, ctmcJumpChain, ωswap, q2]
  have hY : ctmcJumpChain 0 ωswap 1 = 1 := by decide
  have h2 : ctmcJumpTime q2 0 ωswap 2 = 1 + ENNReal.ofReal (1 / 2) := by
    have h := ctmcJumpTime_add (Q := q2) 0 ωswap 1 1
    rw [h1] at h
    refine h.trans ?_
    congr 1
    simp [ctmcJumpTime, ctmcHoldingTime, ctmcShift, ctmcJumpChain, ωswap, q2]
  refine ctmcPath_eq_of_mem (n := 1) 0 ωswap (by rw [h1]; simp) ?_
  rw [h2]
  simpa using ENNReal.lt_add_right ENNReal.one_ne_top (by norm_num)

-- Boundary: under the zero generator the holding times are infinite and the path is constant.
example (ω : ℕ → (Fin 2 → Fin 2) × ℝ) (i : Fin 2) :
    ctmcHoldingTime (0 : Matrix (Fin 2) (Fin 2) ℝ) i ω 0 = ∞ := by
  simp [ctmcHoldingTime]
example (ω : ℕ → (Fin 2 → Fin 2) × ℝ) (i : Fin 2) (t : ℝ≥0) :
    ctmcPath (0 : Matrix (Fin 2) (Fin 2) ℝ) i ω t = i :=
  ctmcPath_eq_of_mem (n := 0) i ω (by simp [ctmcJumpTime]) (by simp [ctmcJumpTime, ctmcHoldingTime])

-- Boundary (junk value off the support of the clocks): a negative clock gives holding time `0`.
example : ctmcHoldingTime q2 0 (fun _ => (fun i => 1 - i, -1)) 0 = 0 := by
  simp [ctmcHoldingTime, ctmcJumpChain, q2]

-- The main theorems, instantiated on `q2`.
example (i : Fin 2) : ∀ᵐ ω ∂ctmcInputMeasure isRateMatrix_q2,
    Tendsto (ctmcJumpTime q2 i ω) atTop (𝓝 ∞) :=
  isRateMatrix_q2.ae_tendsto_ctmcJumpTime i

example (i j : Fin 2) (t : ℝ≥0) :
    (ctmcInputMeasure isRateMatrix_q2).real {ω | ctmcPath q2 i ω t = j} =
      ctmcTransition q2 t i j :=
  isRateMatrix_q2.ctmcInputMeasure_real_ctmcPath_eq i j t

-- At time `0` the chain is at its start state almost surely.
example (i : Fin 2) :
    (ctmcInputMeasure isRateMatrix_q2).real {ω | ctmcPath q2 i ω 0 = i} = 1 := by
  rw [isRateMatrix_q2.ctmcInputMeasure_real_ctmcPath_eq]
  simp

-- The fixed-time restart law with `B = univ` recovers the transition law.
example (i k : Fin 2) (s : ℝ≥0) :
    (ctmcInputMeasure isRateMatrix_q2).real
        {ω | ctmcPath q2 i ω s = k ∧ (fun u => ctmcPath q2 i ω (s + u)) ∈ Set.univ} =
      ctmcTransition q2 s i k := by
  rw [isRateMatrix_q2.ctmcInputMeasure_real_ctmcPath_add i k s MeasurableSet.univ]
  simp

-- Two-time finite-dimensional distribution.
example (s : Fin 2 → ℝ≥0) (j : Fin 2 → Fin 2) :
    (ctmcInputMeasure isRateMatrix_q2).real
        {ω | ∀ k, ctmcPath q2 0 ω (∑ l ∈ Iic k, s l) = j k} =
      ctmcTransition q2 (s 0) 0 (j 0) * ctmcTransition q2 (s 1) (j 0) (j 1) := by
  rw [isRateMatrix_q2.ctmcInputMeasure_real_ctmcPath_fdd, Fin.prod_univ_two]
  rfl

#print axioms IsRateMatrix.ae_tendsto_ctmcJumpTime
#print axioms IsRateMatrix.ctmcInputMeasure_ctmcPath_jumpTime_add
#print axioms IsRateMatrix.ctmcInputMeasure_real_ctmcPath_eq
#print axioms IsRateMatrix.ctmcInputMeasure_real_ctmcPath_add
#print axioms IsRateMatrix.ctmcInputMeasure_real_ctmcPath_fdd

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.Path

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.HittingTime
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for hitting times of finite continuous-time Markov chains

On the two-state rate matrix `!![-1, 1; 2, -2]` with target set `{1}`: a hand-computed hitting
time for a concrete step sequence, the mean hitting time `E_0 H = 1` and the second moment
`E_0 H² = 2` of the rate-`1` exponential holding time, obtained from the backward equations.
Boundary cases: a start inside the target (hitting time and its mean `0`), and the zero
generator, where the start state is absorbing and the target is never hit (`H = ∞`).
-/

@[expose] public section

open Finset Matrix ProbabilityTheory MeasureTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.HittingTime

/-- A two-state rate matrix: rate `1` from state `0` to `1`, rate `2` back. -/
def q2 : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 2, -2]

theorem isRateMatrix_q2 : IsRateMatrix q2 where
  nonneg_of_ne i j h := by fin_cases i <;> fin_cases j <;> simp_all [q2]
  sum_row i := by fin_cases i <;> simp [q2, Fin.sum_univ_two]

theorem isRateMatrix_zero : IsRateMatrix (0 : Matrix (Fin 2) (Fin 2) ℝ) where
  nonneg_of_ne _ _ _ := le_rfl
  sum_row _ := by simp

/-- The constant step sequence: every step maps all states to `1`, with clock `3`. -/
def ωc : ℕ → (Fin 2 → Fin 2) × ℝ := fun _ => (fun _ => 1, 3)

/-- From `0` the chain waits `3 / 1 = 3`, jumps to `1 ∈ {1}`, and the hitting time is `3`. -/
example : ctmcHittingTime q2 0 {1} ωc = 3 := by
  have h0 : (0 : Fin 2) ∉ ({1} : Set (Fin 2)) := by simp
  have hS : ctmcHoldingTime q2 0 ωc 0 = 3 := by
    simp [ctmcHoldingTime, ctmcJumpChain, q2, ωc]
  have hS' : 0 < ctmcHoldingTime q2 1 (ctmcShift 1 ωc) 0 := by
    simp [ctmcHoldingTime, ctmcJumpChain, q2, ωc, ctmcShift]
  rw [ctmcHittingTime_eq_add h0, hS]
  simp only [ωc]
  rw [ctmcHittingTime_eq_zero (Set.mem_singleton 1) hS', add_zero]

/-- Boundary: starting inside the target, the hitting time is `0` (positive first clock). -/
example : ctmcHittingTime q2 1 {1} ωc = 0 :=
  ctmcHittingTime_eq_zero (Set.mem_singleton 1)
    (by simp [ctmcHoldingTime, ctmcJumpChain, q2, ωc])

/-- Boundary: under the zero generator the start state is absorbing, the holding time is
infinite and the target is never hit. -/
example (ω : ℕ → (Fin 2 → Fin 2) × ℝ) :
    ctmcHittingTime (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 {1} ω = ∞ := by
  rw [ctmcHittingTime_eq_add (by simp)]
  simp [ctmcHoldingTime]

theorem q2_00 : q2 0 0 = -1 := by simp [q2]

theorem q2_01 : q2 0 1 = 1 := by simp [q2]

/-- The vector `m = (1, 0)` solves the backward equations of the mean hitting time of `{1}`. -/
theorem backward_mean : ∀ i ∉ ({1} : Set (Fin 2)), (q2 *ᵥ ![1, 0]) i = -1 := by
  intro i hi
  fin_cases i
  · simp [q2, mulVec, dotProduct, Fin.sum_univ_two]
  · simp at hi

/-- `f = (2, 0)` solves the product-moment backward equations with `A = B = {1}`. -/
theorem backward_sq :
    ∀ i ∉ ({1} : Set (Fin 2)) ∪ {1},
      (q2 *ᵥ ![2, 0]) i = -((![1, 0] : Fin 2 → ℝ) i + ![1, 0] i) := by
  intro i hi
  fin_cases i
  · simp [q2, mulVec, dotProduct, Fin.sum_univ_two]; norm_num
  · simp at hi

section Moments

variable [MeasurableSpace (Fin 2)] [DiscreteMeasurableSpace (Fin 2)]

/-- The mean hitting time of `{1}` from `0` is `1`, the mean of a rate-`1` exponential. -/
example : ∫⁻ ω, ctmcHittingTime q2 0 {1} ω ∂ctmcInputMeasure isRateMatrix_q2 = 1 := by
  obtain ⟨hle, h0, heq⟩ := isRateMatrix_q2.ctmcHittingTime_backward (A := {1})
    (m := ![1, 0]) (fun i => by fin_cases i <;> simp) backward_mean
  have h := heq 0 (by simp)
  simp only [mulVec, dotProduct, Fin.sum_univ_two, q2_00, q2_01] at h
  rw [h0 1 rfl] at h
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle 0)
  rw [← ENNReal.ofReal_toReal hfin]
  simp at h
  rw [show (∫⁻ ω, ctmcHittingTime q2 0 {1} ω ∂ctmcInputMeasure isRateMatrix_q2).toReal = 1 by
    linarith, ENNReal.ofReal_one]

/-- The second moment of the hitting time of `{1}` from `0` is `2`, that of a rate-`1`
exponential (product moment with `A = B`). -/
example : ∫⁻ ω, ctmcHittingTime q2 0 {1} ω * ctmcHittingTime q2 0 {1} ω
    ∂ctmcInputMeasure isRateMatrix_q2 = 2 := by
  have hm0 : ∀ i, (0 : ℝ) ≤ (![1, 0] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> simp
  obtain ⟨hle, h0, heq⟩ := isRateMatrix_q2.ctmcHittingTime_mul_backward (A := {1}) (B := {1})
    hm0 hm0 (f := ![2, 0]) (fun i => by fin_cases i <;> simp) backward_mean backward_mean
    backward_sq
  obtain ⟨hleA, h0A, heqA⟩ := isRateMatrix_q2.ctmcHittingTime_backward (A := {1})
    (m := ![1, 0]) hm0 backward_mean
  have hA := heqA 0 (by simp)
  simp only [mulVec, dotProduct, Fin.sum_univ_two, q2_00, q2_01] at hA
  rw [h0A 1 rfl] at hA
  have h := heq 0 (by simp)
  simp only [mulVec, dotProduct, Fin.sum_univ_two, q2_00, q2_01] at h
  rw [h0 1 (by simp)] at h
  simp at hA h
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle 0)
  rw [← ENNReal.ofReal_toReal hfin]
  rw [show (∫⁻ ω, ctmcHittingTime q2 0 {1} ω * ctmcHittingTime q2 0 {1} ω
    ∂ctmcInputMeasure isRateMatrix_q2).toReal = 2 by linarith]
  simp

/-- Boundary: from a state of the target, the mean hitting time is `0`. -/
example : ∫⁻ ω, ctmcHittingTime q2 1 {1} ω ∂ctmcInputMeasure isRateMatrix_q2 = 0 :=
  isRateMatrix_q2.lintegral_ctmcHittingTime_of_mem rfl

/-- Boundary: under the zero generator, the mean hitting time of an unreachable state is `∞`
(the first-step equations need a positive exit rate off the target). -/
example : ∫⁻ ω, ctmcHittingTime (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 {1} ω
    ∂ctmcInputMeasure isRateMatrix_zero = ∞ := by
  have h : ∀ ω, ctmcHittingTime (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 {1} ω = ∞ := fun ω => by
    rw [ctmcHittingTime_eq_add (by simp)]
    simp [ctmcHoldingTime]
  simp [h]

end Moments

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.HittingTime

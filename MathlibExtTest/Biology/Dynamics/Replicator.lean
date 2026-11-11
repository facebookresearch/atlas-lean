/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.Replicator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Tests for replicator dynamics: a non-vacuity witness (two strategies with constant fitness
`1` and `0`, whose solution is the logistic curve), simplex and face invariance on it, and
rest points of a symmetric game. -/

open Real Set

namespace MathlibExtTest.Biology.Dynamics.Replicator

open MathlibExt.Biology.Dynamics.Replicator

/-- Constant fitness `1` for strategy `0` and `0` for strategy `1`. -/
noncomputable def fit : (Fin 2 → ℝ) → Fin 2 → ℝ := fun _ => ![1, 0]

/-- The logistic solution `x₀ = e^t / (1 + e^t)`, `x₁ = 1 / (1 + e^t)`. -/
noncomputable def logistic (t : ℝ) : Fin 2 → ℝ := ![exp t / (1 + exp t), 1 / (1 + exp t)]

/-- **Non-vacuity witness.** The logistic curve solves the replicator equation for `fit`. -/
theorem isSolution_logistic : IsSolution fit logistic where
  hasDerivAt i t _ := by
    have hpos : (1 + exp t) ≠ 0 := by positivity
    have hd : HasDerivAt (fun s => 1 + exp s) (exp t) t := (hasDerivAt_exp t).const_add 1
    fin_cases i
    · have h := (hasDerivAt_exp t).fun_div hd hpos
      simp only [Fin.zero_eta, Fin.isValue, logistic, fit, meanFitness, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      convert h using 1
      field_simp
      ring
    · have h := (hasDerivAt_const t (1 : ℝ)).fun_div hd hpos
      simp only [Fin.mk_one, Fin.isValue, logistic, fit, meanFitness, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      convert h using 1
      field_simp
      ring

example : Continuous fit := continuous_const

/-- The witness starts on the simplex, so it stays there. -/
example (t : ℝ) (ht : 0 ≤ t) : ∑ i, logistic t i = 1 :=
  isSolution_logistic.sum_eq_one continuous_const (by
    simp [logistic, Fin.sum_univ_two]
    field_simp) ht

/-- The witness stays in the simplex, and both strategies stay present. -/
example (t : ℝ) (ht : 0 ≤ t) : (∀ i, 0 ≤ logistic t i) ∧ ∑ i, logistic t i = 1 :=
  isSolution_logistic.mem_simplex continuous_const
    (fun i => by fin_cases i <;> simp [logistic])
    (by simp [logistic, Fin.sum_univ_two]; field_simp) ht

example (t : ℝ) (ht : 0 ≤ t) : 0 < logistic t 1 :=
  isSolution_logistic.pos_of_pos continuous_const (by simp [logistic]) ht

/-- A pure state (strategy `1` absent) stays pure under a constant-fitness game. -/
example (x : ℝ → Fin 2 → ℝ) (h : IsSolution fit x) (h0 : x 0 1 = 0) (t : ℝ) (ht : 0 ≤ t) :
    x t 1 = 0 :=
  h.eq_zero_of_eq_zero continuous_const h0 ht

/-- In a game where both strategies always have fitness `2`, the barycenter is a rest point,
and it is an equalizer. -/
example : IsRestPoint (fun _ => fun _ => (2 : ℝ)) (![1 / 2, 1 / 2] : Fin 2 → ℝ) := by
  rw [isRestPoint_iff (fun i => by fin_cases i <;> norm_num)]
  intro i
  simp [meanFitness, Fin.sum_univ_two]
  norm_num

/-- With fitness `![1, 0]` an interior state is never a rest point. -/
example : ¬ IsRestPoint fit (![1 / 2, 1 / 2] : Fin 2 → ℝ) := by
  rw [isRestPoint_iff (fun i => by fin_cases i <;> norm_num)]
  intro h
  have h0 := h 0
  have h1 := h 1
  simp [fit, meanFitness, Fin.sum_univ_two] at h0 h1

end MathlibExtTest.Biology.Dynamics.Replicator

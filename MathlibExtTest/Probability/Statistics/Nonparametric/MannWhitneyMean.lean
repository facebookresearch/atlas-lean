/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Nonparametric.MannWhitneyMean

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Positive case: a single pair reduces to the kernel itself. -/
example (a b : ℝ) :
    mannWhitneyU (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
      = (if b < a then (1 : ℝ) else if b = a then 1 / 2 else 0) := by
  simp [mannWhitneyU]

/-- Boundary case: an empty first sample gives `U = 0`. -/
example {n : ℕ} (y : Fin n → ℝ) : mannWhitneyU (Fin.elim0 : Fin 0 → ℝ) y = 0 := by
  simp [mannWhitneyU]

/-- Degenerate case: fully tied constant samples give `U / (m n) = 1 / 2`. -/
example (a : ℝ) (m n : ℕ) :
    mannWhitneyU (fun _ : Fin m => a) (fun _ : Fin n => a) = (m * n : ℝ) / 2 := by
  simp only [mannWhitneyU, lt_irrefl, ite_false, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

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

/-- Degenerate case: fully tied constant samples give `U = m * n / 2`
(equivalently `U / (m * n) = 1 / 2` for nonempty samples). -/
example (a : ℝ) (m n : ℕ) :
    mannWhitneyU (fun _ : Fin m => a) (fun _ : Fin n => a) = (m * n : ℝ) / 2 := by
  simp only [mannWhitneyU, lt_irrefl, ite_false, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Positive case: the mean theorem applied to an explicit independent pair
over a product sample space. -/
example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (Z : Fin 1 ⊕ Fin 1 → (Fin 2 → ℝ) → ℝ)
    (hIndep : iIndepFun Z (Measure.pi fun _ : Fin 2 => ν))
    (hX : ∀ i, HasLaw (Z (Sum.inl i)) ν (Measure.pi fun _ : Fin 2 => ν))
    (hY : ∀ j, HasLaw (Z (Sum.inr j)) ν (Measure.pi fun _ : Fin 2 => ν)) :
    ∫ ω, ProbabilityTheory.mannWhitneyU (fun i => Z (Sum.inl i) ω) (fun j => Z (Sum.inr j) ω)
      ∂(Measure.pi fun _ : Fin 2 => ν)
    = ∫ a, ∫ b, (if b < a then (1 : ℝ) else if b = a then 1 / 2 else 0) ∂ν ∂ν := by
  have h := ProbabilityTheory.mannWhitneyU_mean (μx := ν) (μy := ν) hIndep hX hY
  simpa using h

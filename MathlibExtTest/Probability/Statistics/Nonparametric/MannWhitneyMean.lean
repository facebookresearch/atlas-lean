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

/-- Positive case: the mean theorem on the explicit coordinate pair over a
product law, with independence and laws discharged from that model. -/
example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∫ ω, ProbabilityTheory.mannWhitneyU (fun _ : Fin 1 => (ω : Fin 2 → ℝ) 0)
      (fun _ : Fin 1 => ω 1) ∂(Measure.pi fun _ : Fin 2 => ν)
    = ∫ a, ∫ b, (if b < a then (1 : ℝ) else if b = a then 1 / 2 else 0) ∂ν ∂ν := by
  have e_inj : Function.Injective
      (Sum.elim (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2))
        : Fin 1 ⊕ Fin 1 → Fin 2) := by
    decide
  have hbase : iIndepFun (fun i (ω : Fin 2 → ℝ) => id (ω i))
      (Measure.pi fun _ : Fin 2 => ν) :=
    iIndepFun_pi (X := fun (_ : Fin 2) => (id : ℝ → ℝ)) (μ := fun _ : Fin 2 => ν)
      (fun _ => measurable_id.aemeasurable)
  have hIndep : iIndepFun
      (fun s : Fin 1 ⊕ Fin 1 => fun ω : Fin 2 → ℝ =>
        ω (Sum.elim (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2)) s))
      (Measure.pi fun _ : Fin 2 => ν) :=
    hbase.precomp e_inj
  have hX : ∀ i : Fin 1, HasLaw
      ((fun s (ω : Fin 2 → ℝ) =>
        ω (Sum.elim (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2)) s))
        (Sum.inl i))
      ν (Measure.pi fun _ : Fin 2 => ν) := by
    intro i
    show HasLaw (fun ω : Fin 2 → ℝ => ω 0) ν (Measure.pi fun _ : Fin 2 => ν)
    exact ⟨(measurable_pi_apply 0).aemeasurable, (measurePreserving_eval _ 0).map_eq⟩
  have hY : ∀ j : Fin 1, HasLaw
      ((fun s (ω : Fin 2 → ℝ) =>
        ω (Sum.elim (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2)) s))
        (Sum.inr j))
      ν (Measure.pi fun _ : Fin 2 => ν) := by
    intro j
    show HasLaw (fun ω : Fin 2 → ℝ => ω 1) ν (Measure.pi fun _ : Fin 2 => ν)
    exact ⟨(measurable_pi_apply 1).aemeasurable, (measurePreserving_eval _ 1).map_eq⟩
  have h := ProbabilityTheory.mannWhitneyU_mean (μx := ν) (μy := ν)
    (Z := fun s (ω : Fin 2 → ℝ) =>
      ω (Sum.elim (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2)) s))
    hIndep hX hY
  simpa using h

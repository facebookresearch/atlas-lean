/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Reliability.MonteCarloFailure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.NormNum

/-! # Regression for IID sampling of a limit state with an atom at zero -/

open MeasureTheory ProbabilityTheory Reliability

private noncomputable def half : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩

-- For sixteen independent samples, the sample-size condition holds at tolerance 1/4
-- and bounds the absolute-error probability by 3/4.
example :
    let ν := bernoulliMeasure (0 : ℝ) 1 half
    let P := Measure.pi (fun _ : Fin 16 => ν)
    P.real {ω | ω 0 ≤ 0} = 1 / 2 ∧
      P.real {ω | (1 / 4 : ℝ) <
        |(∑ i : Fin 16, if ω i ≤ 0 then (1 : ℝ) else 0) / 16 - 1 / 2|} ≤ 3 / 4 := by
  classical
  intro ν P
  let X : Fin 16 → (Fin 16 → ℝ) → ℝ := fun i ω => ω i
  have hmp (i : Fin 16) : MeasurePreserving (X i) P ν :=
    measurePreserving_eval (fun _ : Fin 16 => ν) i
  have hind : iIndepFun X P := iIndepFun_pi (X := fun _ : Fin 16 => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)
  have hident (i : Fin 16) : IdentDistrib (X i) (X 0) P P :=
    ⟨(hmp i).aemeasurable, (hmp 0).aemeasurable, (hmp i).map_eq.trans (hmp 0).map_eq.symm⟩
  have hs : MeasurableSet {z : ℝ | z ≤ 0} := measurableSet_Iic
  have hp : P.real (X 0 ⁻¹' {z : ℝ | z ≤ 0}) = 1 / 2 := by
    rw [← map_measureReal_apply (hmp 0).measurable hs, (hmp 0).map_eq]
    have h0 : (0 : ℝ) ∈ {z : ℝ | z ≤ 0} := by
      change (0 : ℝ) ≤ 0
      exact le_rfl
    have h1 : (1 : ℝ) ∉ {z : ℝ | z ≤ 0} := by
      change ¬ (1 : ℝ) ≤ 0
      norm_num
    exact bernoulliMeasure_real_apply_of_mem_of_notMem half hs h0 h1
  refine ⟨hp, ?_⟩
  have hsize : Real.log (2 / (3 / 4 : ℝ)) / (2 * (1 / 4 : ℝ) ^ 2) ≤ (16 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2 * (1 / 4 : ℝ) ^ 2)).mpr
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2 / (3 / 4 : ℝ))).trans
      (by norm_num)
  have h := (monte_carlo_failure_probability (by decide : 0 < 16) X hind hident id
    measurable_id (ε := 1 / 4) (by norm_num)).2 (3 / 4) (by norm_num) (by norm_num) hsize
  change P.real {ω | (1 / 4 : ℝ) <
    |(∑ i : Fin 16, ({z : ℝ | z ≤ 0} : Set ℝ).indicator (fun _ => (1 : ℝ)) (X i ω)) / 16 -
      P.real (X 0 ⁻¹' {z : ℝ | z ≤ 0})|} ≤ 3 / 4 at h
  simpa only [hp, X, Set.indicator, Set.mem_ofPred_eq] using h

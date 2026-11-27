/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.CompetingExponentialClocks
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # One-clock and unequal-rate exponential races -/

open MeasureTheory ProbabilityTheory Set

private theorem coordinateRace {n : ℕ} (q : Fin (n + 1) → ℝ) (hq : ∀ i, 0 < q i) :
    let μ := Measure.pi (fun i => expMeasure (q i))
    let T (x : Fin (n + 1) → ℝ) := Finset.univ.inf' Finset.univ_nonempty x
    ∃ J : (Fin (n + 1) → ℝ) → Fin (n + 1),
      HasLaw T (expMeasure (∑ i, q i)) μ ∧ IndepFun T J μ ∧
      (∀ j, μ.real (J ⁻¹' {j}) = q j / ∑ i, q i) ∧
      ∀ (j : Fin (n + 1)) (t : ℝ), 0 ≤ t →
        μ.real (T ⁻¹' Ioi t ∩ J ⁻¹' {j}) =
          (q j / ∑ i, q i) * Real.exp (-((∑ i, q i) * t)) := by
  let _ (i : Fin (n + 1)) := isProbabilityMeasure_expMeasure (hq i)
  obtain ⟨J, _, _, hT, hind, hJ, hjoint⟩ :=
    competing_exponential_clocks (μ := Measure.pi fun i => expMeasure (q i))
      (X := fun i x => x i) q hq measurable_pi_apply
      (fun i => ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩)
      (iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable))
  exact ⟨J, hT, hind, hJ, hjoint⟩

-- The empty product of losing-clock survival factors is one.
example :
    let μ := Measure.pi (fun _ : Fin 1 => expMeasure 2)
    let T (x : Fin 1 → ℝ) := Finset.univ.inf' Finset.univ_nonempty x
    ∃ J : (Fin 1 → ℝ) → Fin 1, HasLaw T (expMeasure 2) μ ∧
      μ.real (J ⁻¹' {0}) = 1 ∧ μ.real (T ⁻¹' Ioi 1 ∩ J ⁻¹' {0}) = Real.exp (-2) := by
  obtain ⟨J, hT, _, hJ, hjoint⟩ :=
    coordinateRace (fun _ : Fin 1 => 2) (fun _ => by norm_num)
  refine ⟨J, ?_, ?_, ?_⟩
  · simpa using hT
  · simpa using hJ 0
  · simpa using hjoint 0 1 zero_le_one

-- Unequal rates distinguish the two winner probabilities, including at a positive time.
example :
    let q (i : Fin 2) : ℝ := if i = 0 then 1 else 2
    let μ := Measure.pi (fun i => expMeasure (q i))
    let T (x : Fin 2 → ℝ) := Finset.univ.inf' Finset.univ_nonempty x
    ∃ J : (Fin 2 → ℝ) → Fin 2, HasLaw T (expMeasure 3) μ ∧ IndepFun T J μ ∧
      μ.real (J ⁻¹' {0}) = 1 / 3 ∧ μ.real (J ⁻¹' {1}) = 2 / 3 ∧
      μ.real (T ⁻¹' Ioi 1 ∩ J ⁻¹' {1}) = (2 / 3) * Real.exp (-3) := by
  intro q μ T
  have hq (i : Fin 2) : 0 < q i := by fin_cases i <;> norm_num [q]
  have hsum : ∑ i, q i = 3 := by norm_num [Fin.sum_univ_two, q]
  obtain ⟨J, hT, hind, hJ, hjoint⟩ := coordinateRace q hq
  refine ⟨J, ?_, hind, ?_, ?_, ?_⟩
  · simpa only [hsum] using hT
  · simpa [hsum, q] using hJ 0
  · simpa [hsum, q] using hJ 1
  · simpa [hsum, q] using hjoint 1 1 zero_le_one

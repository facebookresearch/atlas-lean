/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Reliability.FiniteSystemReliability
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.NormNum

/-! # Regressions for finite system reliability -/

open MeasureTheory ProbabilityTheory Reliability Set
open scoped ENNReal NNReal

private noncomputable def half : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩

-- A lifetime of 1 is down at time 1. For three fair independent components,
-- the series, parallel, and 2-of-3 survival probabilities are distinct.
example :
    let ν := bernoulliMeasure (2 : ℝ) 1 half
    let P := Measure.pi (fun _ : Fin 3 => ν)
    let L := fun A (ω : Fin 3 → ℝ) => systemLifetime (Fin 3) A (fun i => ENNReal.ofReal (ω i))
    P.real {ω | (1 : ℝ≥0∞) < L (seriesEvent (Fin 3)) ω} = 1 / 8 ∧
      P.real {ω | (1 : ℝ≥0∞) < L (parallelEvent (Fin 3)) ω} = 7 / 8 ∧
      P.real {ω | (1 : ℝ≥0∞) < L (kOutOfNEvent (Fin 3) 2) ω} = 1 / 2 := by
  intro ν P L
  let T : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i ω => ω i
  have hmp (i : Fin 3) : MeasurePreserving (T i) P ν :=
    measurePreserving_eval (fun _ : Fin 3 => ν) i
  have hind : iIndepFun T P := iIndepFun_pi (X := fun _ : Fin 3 => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)
  have hp (i : Fin 3) : P.real {ω | (1 : ℝ) < T i ω} = 1 / 2 := by
    change P.real (T i ⁻¹' Ioi (1 : ℝ)) = 1 / 2
    rw [← map_measureReal_apply (hmp i).measurable measurableSet_Ioi, (hmp i).map_eq]
    exact bernoulliMeasure_real_apply_of_mem_of_notMem half measurableSet_Ioi
      (by change (1 : ℝ) < 2; norm_num) (by change ¬ (1 : ℝ) < 1; simp)
  have hs := series_parallel_system_reliability hind (fun i => (hmp i).measurable) 1
  have hk := kOutOfN_system_reliability (k := 2) hind (fun i => (hmp i).measurable) 1 (1 / 2) hp
  simp only [NNReal.coe_one, ENNReal.coe_one, hp, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hs
  have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
  have htail : (∑ j ∈ Finset.Icc 2 3, (Nat.choose 3 j : ℝ) * (1 / 2) ^ j *
      (1 - 1 / 2) ^ (3 - j)) = 1 / 2 := by
    rw [hIcc]
    norm_num [Finset.sum_insert, Nat.choose]
  rw [htail] at hk
  norm_num at hs
  exact ⟨hs.1, hs.2, by simpa using hk⟩

-- The survival integral of a deterministic lifetime of two is its extended mean.
example : (∫⁻ t in Ioi 0, (Measure.dirac () : Measure Unit) {_ω | t < (2 : ℝ)}) = 2 := by
  have h := mean_lifetime_eq_survival_integral (Measure.dirac ())
    (T := fun _ => (2 : ℝ)) measurable_const (Filter.Eventually.of_forall fun _ => by norm_num)
  rw [← h.1]
  simp

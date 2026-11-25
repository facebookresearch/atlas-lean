/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkovFilter
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Cslib.MachineLearning.Sequence.HiddenMarkovFilter

open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.Sequence.HiddenMarkovLaw
open Cslib.MachineLearning.Sequence.HiddenMarkovMeasure
open ProbabilityTheory

/-! ## Nonvacuity examples

`exA` (states and observations `Bool`): uniform start, `true → true` with
probability one (a zero transition cell `true → false`), `false` moves to
either state with probability `1/2`, and each state emits its own label
with probability `3/4`. On the all-`true` stream, the filter at time 0 is
`3/4`, the smoother with one future observation is `9/11`, the one-step
prediction is `7/8`, and the evidence of `x 0 = true` is `1/2`.

`exZ`: start in `true` with probability one, with identity transitions
and identity emissions. The word `x 0 = false` has evidence `0`;
totalized division makes every `smoothed` weight `0`, while the posterior
kernel is a probability measure at every word, so the correspondence
fails there and the positive-evidence hypothesis cannot be dropped. -/

/-- Example with full emission support and a zero transition cell. -/
private noncomputable def exA : HMM Bool Bool ℝ where
  init _ := 1 / 2
  trans s s' := if s then (if s' then 1 else 0) else 1 / 2
  emit s o := if s = o then 3 / 4 else 1 / 4

/-- Example with zero evidence for the word `false`. -/
private noncomputable def exZ : HMM Bool Bool ℝ where
  init s := if s then 1 else 0
  trans s s' := if s = s' then 1 else 0
  emit s o := if s = o then 1 else 0

/-- Proved, so the tests below do not rest on a vacuous normalization witness. -/
private theorem exA_normalized : Normalized exA where
  init_nonneg _ := by norm_num [exA]
  init_sum := by norm_num [exA]
  trans_nonneg s s' := by cases s <;> cases s' <;> norm_num [exA]
  trans_sum s := by cases s <;> norm_num [exA]
  emit_nonneg s o := by cases s <;> cases o <;> norm_num [exA]
  emit_sum s := by cases s <;> norm_num [exA]

/-- Proved, as for `exA_normalized`. -/
private theorem exZ_normalized : Normalized exZ where
  init_nonneg s := by cases s <;> norm_num [exZ]
  init_sum := by norm_num [exZ]
  trans_nonneg s s' := by cases s <;> cases s' <;> norm_num [exZ]
  trans_sum s := by cases s <;> norm_num [exZ]
  emit_nonneg s o := by cases s <;> cases o <;> norm_num [exZ]
  emit_sum s := by cases s <;> norm_num [exZ]

/-- The positive-evidence hypothesis of `posterior_prediction_match` is satisfiable. -/
private theorem test_exA_evidence :
    likelihood exA (extend 0 (fun _ => true)) 0 = 1 / 2 := by
  rw [likelihood_eq_sum_forward]
  norm_num [forward, exA, Cslib.MachineLearning.Sequence.HiddenMarkovLaw.extend]

/-- Smoothed side, filter at time 0 (no future data). -/
private theorem test_exA_filter_smoothed :
    smoothed (extend 0 (fun _ => true)) exA 0 0 true = 3 / 4 := by
  rw [smoothed, likelihood_eq_sum_forward]
  norm_num [forward, backward, exA, Cslib.MachineLearning.Sequence.HiddenMarkovLaw.extend]

/-- Smoothed side, smoother at time 0 with the observation at time 1. -/
private theorem test_exA_smoother_smoothed :
    smoothed (extend 1 (fun _ => true)) exA 0 1 true = 9 / 11 := by
  rw [smoothed, likelihood_eq_sum_forward]
  norm_num [forward, backward, exA, Cslib.MachineLearning.Sequence.HiddenMarkovLaw.extend]

/-- Smoothed side, one-step prediction of state `true` at time 1. -/
private theorem test_exA_prediction_smoothed :
    prediction (extend 0 (fun _ => true)) exA 0 true = 7 / 8 := by
  simp only [prediction, smoothed, likelihood_eq_sum_forward]
  norm_num [forward, backward, exA, Cslib.MachineLearning.Sequence.HiddenMarkovLaw.extend]

/-- Positive evidence for `exA` at the all-`true` word of length one. -/
private theorem test_exA_hx : 0 < likelihood exA (extend 0 (fun _ => true)) 0 := by
  rw [test_exA_evidence]
  norm_num

/-- Filter conjunct applied to `exA`: the posterior filter mass of state `true` at time 0 is
`3/4`, derived from `posterior_prediction_match` and the smoothed-side value. -/
private theorem test_match_filter_exA :
    (∑ z ∈ Finset.univ.filter (fun z : Fin 1 → Bool => z (Fin.last 0) = true),
        (filterPosterior exA exA_normalized 0 (fun _ => true) {z}).toReal) = 3 / 4 := by
  rw [← (posterior_prediction_match exA exA_normalized 0 (fun _ => true) test_exA_hx).1 true]
  exact test_exA_filter_smoothed

/-- Prediction conjunct applied to `exA`: the predictive posterior mass of state `true` at
time 1 is `7/8`, derived from `posterior_prediction_match` and the smoothed-side value. -/
private theorem test_match_prediction_exA :
    (∑ z ∈ Finset.univ.filter (fun z : Fin 2 → Bool => z (Fin.last 1) = true),
        (predictivePosterior exA exA_normalized 0 (fun _ => true) {z}).toReal) = 7 / 8 := by
  rw [← (posterior_prediction_match exA exA_normalized 0 (fun _ => true) test_exA_hx).2 true]
  exact test_exA_prediction_smoothed

/-- Filter versus future-data smoother: on the same all-`true` stream, the posterior filter
mass of state `true` at time 0 is `3/4`, while the smoother that also uses the observation at
time 1 gives `9/11`. -/
private theorem test_filter_vs_smoother :
    (∑ z ∈ Finset.univ.filter (fun z : Fin 1 → Bool => z (Fin.last 0) = true),
        (filterPosterior exA exA_normalized 0 (fun _ => true) {z}).toReal) = 3 / 4 ∧
      smoothed (extend 0 (fun _ => true)) exA 0 0 true = 3 / 4 ∧
      smoothed (extend 1 (fun _ => true)) exA 0 1 true = 9 / 11 :=
  ⟨test_match_filter_exA, test_exA_filter_smoothed, test_exA_smoother_smoothed⟩

/-- One transition is applied: the predictive posterior mass of state `true` at time 1 is
`7/8`, not the filter value `3/4`. -/
private theorem test_prediction_one_transition :
    (∑ z ∈ Finset.univ.filter (fun z : Fin 2 → Bool => z (Fin.last 1) = true),
        (predictivePosterior exA exA_normalized 0 (fun _ => true) {z}).toReal) = 7 / 8 ∧
      prediction (extend 0 (fun _ => true)) exA 0 true = 7 / 8 :=
  ⟨test_match_prediction_exA, test_exA_prediction_smoothed⟩

private theorem proof_zero_total :
    ∑ z : Fin 1 → Bool, (filterPosterior exZ exZ_normalized 0 (fun _ => false) {z}).toReal = 1 := by
  have hmark : ProbabilityTheory.IsMarkovKernel (filterPosterior exZ exZ_normalized 0) := by
    unfold filterPosterior
    infer_instance
  have hsum : ∑ z ∈ (Finset.univ : Finset (Fin 1 → Bool)),
      filterPosterior exZ exZ_normalized 0 (fun _ => false) {z} = 1 := by
    rw [MeasureTheory.sum_measure_singleton, Finset.coe_univ, MeasureTheory.measure_univ]
  have hfin : ∀ z ∈ (Finset.univ : Finset (Fin 1 → Bool)),
      filterPosterior exZ exZ_normalized 0 (fun _ => false) {z} ≠ ⊤ :=
    fun z _ => MeasureTheory.measure_ne_top _ _
  have hreal := ENNReal.toReal_sum hfin
  rw [hsum] at hreal
  simpa using hreal.symm

private theorem proof_zero_fiber :
    (∑ s : Bool, ∑ z ∈ Finset.univ.filter (fun z : Fin 1 → Bool => z (Fin.last 0) = s),
      (filterPosterior exZ exZ_normalized 0 (fun _ => false) {z}).toReal)
    = ∑ z : Fin 1 → Bool, (filterPosterior exZ exZ_normalized 0 (fun _ => false) {z}).toReal := by
  exact Finset.sum_fiberwise Finset.univ (fun z : Fin 1 → Bool => z (Fin.last 0))
    (fun z => (filterPosterior exZ exZ_normalized 0 (fun _ => false) {z}).toReal)

/-- Zero evidence is excluded, not normalized by totalized division: the evidence is `0`,
every `smoothed` weight is the totalized `0 / 0 = 0`, and the filter correspondence fails. -/
private theorem test_zero_evidence_excluded :
    likelihood exZ (extend 0 (fun _ => false)) 0 = 0 ∧
      (∀ s, smoothed (extend 0 (fun _ => false)) exZ 0 0 s = 0) ∧
      ¬ (∀ s, smoothed (extend 0 (fun _ => false)) exZ 0 0 s =
        ∑ z ∈ Finset.univ.filter (fun z : Fin 1 → Bool => z (Fin.last 0) = s),
          (filterPosterior exZ exZ_normalized 0 (fun _ => false) {z}).toReal) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [likelihood_eq_sum_forward]
    norm_num [forward, exZ, Cslib.MachineLearning.Sequence.HiddenMarkovLaw.extend]
  · intro s
    have hL : likelihood exZ (extend 0 (fun _ => false)) 0 = 0 := by
      rw [likelihood_eq_sum_forward]
      norm_num [forward, exZ, Cslib.MachineLearning.Sequence.HiddenMarkovLaw.extend]
    simp only [smoothed, hL, div_zero]
  · intro hcorr
    have hL : likelihood exZ (extend 0 (fun _ => false)) 0 = 0 := by
      rw [likelihood_eq_sum_forward]
      norm_num [forward, exZ, Cslib.MachineLearning.Sequence.HiddenMarkovLaw.extend]
    have hzero : ∀ s, smoothed (extend 0 (fun _ => false)) exZ 0 0 s = 0 := by
      intro s
      simp only [smoothed, hL, div_zero]
    have hsum0 : ∑ s : Bool, smoothed (extend 0 (fun _ => false)) exZ 0 0 s = 0 := by
      simp [hzero]
    have hsum1 : ∑ s : Bool, smoothed (extend 0 (fun _ => false)) exZ 0 0 s = 1 := by
      calc ∑ s : Bool, smoothed (extend 0 (fun _ => false)) exZ 0 0 s
          = ∑ s : Bool, ∑ z ∈ Finset.univ.filter
              (fun z : Fin 1 → Bool => z (Fin.last 0) = s),
              (filterPosterior exZ exZ_normalized 0 (fun _ => false) {z}).toReal := by
            simp only [hcorr]
        _ = ∑ z : Fin 1 → Bool,
              (filterPosterior exZ exZ_normalized 0 (fun _ => false) {z}).toReal :=
            proof_zero_fiber
        _ = 1 := proof_zero_total
    rw [hsum0] at hsum1
    exact zero_ne_one hsum1

end Cslib.MachineLearning.Sequence.HiddenMarkovFilter

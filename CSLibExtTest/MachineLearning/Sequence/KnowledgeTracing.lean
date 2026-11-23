/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.BaumWelch
public import CSLibExt.MachineLearning.Sequence.KnowledgeTracing
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Cslib.MachineLearning.Sequence.KnowledgeTracing

open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.Sequence.HiddenMarkovLaw
open Cslib.MachineLearning.Sequence.HiddenMarkovFilter

/-! ## Nonvacuity examples

Main fixture `p = 1/4, L = 1/5, g = 1/4, s = 1/10`: a correct response
gives `6/11 → 7/11`, and an incorrect one gives `2/47 → 11/47`.
Applying the learning transition before the emission (prior `2/5`)
would give `12/17` after a correct response, exposing wrong indexing.
Boundary cases cover no forgetting, uninformative responses
`g = 1 - s`, `L = 0` and `L = 1`, and zero evidence `p = g = 0` for a
correct response. -/

private theorem i14 : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
private theorem i15 : (1 / 5 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
private theorem i110 : (1 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
private theorem i34 : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
private theorem i0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
private theorem i1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num

/-- Main fixture, correct response: posterior `6/11`, from `filter_formulas`. -/
private theorem test_correct_posterior :
    learnedPosterior (1 / 4) (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i14 i15 i14 i110) true =
      6 / 11 := by
  rw [((filter_formulas i14 i15 i14 i110).1 (by norm_num)).1]
  norm_num [correctPosterior]

/-- Main fixture, correct response: learning-updated prior `7/11`, from `filter_formulas`. -/
private theorem test_correct_next :
    learnedNextPrior (1 / 4) (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i14 i15 i14 i110) true =
      7 / 11 := by
  rw [((filter_formulas i14 i15 i14 i110).1 (by norm_num)).2]
  norm_num [correctPosterior, learnStep]

/-- Main fixture, incorrect response: posterior `2/47`, from `filter_formulas`. -/
private theorem test_incorrect_posterior :
    learnedPosterior (1 / 4) (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i14 i15 i14 i110) false =
      2 / 47 := by
  rw [((filter_formulas i14 i15 i14 i110).2 (by norm_num)).1]
  norm_num [incorrectPosterior]

/-- Main fixture, incorrect response: learning-updated prior `11/47`, from `filter_formulas`. -/
private theorem test_incorrect_next :
    learnedNextPrior (1 / 4) (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i14 i15 i14 i110) false =
      11 / 47 := by
  rw [((filter_formulas i14 i15 i14 i110).2 (by norm_num)).2]
  norm_num [incorrectPosterior, learnStep]

/-- Main fixture evidence through `likelihood_response`: `33/80` for a correct response and
`47/80` for an incorrect one, both positive. -/
private theorem test_evidence :
    likelihood (bkt (1 / 4) (1 / 5) (1 / 4) (1 / 10)) (extend 0 (fun _ => true)) 0 = 33 / 80 ∧
      likelihood (bkt (1 / 4) (1 / 5) (1 / 4) (1 / 10)) (extend 0 (fun _ => false)) 0 =
        47 / 80 := by
  rw [likelihood_response, likelihood_response]
  norm_num

/-- Cross-check through the shared filter bridge, independent of `filter_formulas` and the closed
forms: `posterior_prediction_match` applied to the main fixture turns the posterior masses into
forward-backward weights, which evaluate to `6/11` and `7/11`. -/
private theorem test_bridge_cross_check :
    learnedPosterior (1 / 4) (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i14 i15 i14 i110) true =
        6 / 11 ∧
      learnedNextPrior (1 / 4) (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i14 i15 i14 i110) true =
        7 / 11 := by
  have hx : 0 < likelihood (bkt (1 / 4) (1 / 5) (1 / 4) (1 / 10)) (extend 0 (fun _ => true)) 0 := by
    rw [likelihood_response]
    norm_num
  have hb := posterior_prediction_match (bkt (1 / 4) (1 / 5) (1 / 4) (1 / 10))
    (normalized_bkt i14 i15 i14 i110) 0 (fun _ => true) hx
  constructor
  · rw [learnedPosterior, ← hb.1 true, smoothed, likelihood_eq_sum_forward]
    norm_num [forward, backward, bkt, Cslib.MachineLearning.Sequence.HiddenMarkovLaw.extend]
  · rw [learnedNextPrior, ← hb.2 true]
    simp only [prediction, smoothed, likelihood_eq_sum_forward]
    norm_num [forward, backward, bkt, Cslib.MachineLearning.Sequence.HiddenMarkovLaw.extend]

/-- Emission before the learning transition: the posterior after a correct response is `6/11`;
the transition-before-emission order (prior `learnStep L p = 2/5`) gives `12/17`. -/
private theorem test_transition_before_emission :
    learnedPosterior (1 / 4) (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i14 i15 i14 i110) true =
        6 / 11 ∧
      learnStep (1 / 5) (1 / 4) = 2 / 5 ∧
      correctPosterior (learnStep (1 / 5) (1 / 4)) (1 / 4) (1 / 10) = 12 / 17 ∧
      learnedPosterior (1 / 4) (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i14 i15 i14 i110) true ≠
        correctPosterior (learnStep (1 / 5) (1 / 4)) (1 / 4) (1 / 10) := by
  have h1 := test_correct_posterior
  have h2 : correctPosterior (learnStep (1 / 5) (1 / 4)) (1 / 4) (1 / 10) = 12 / 17 := by
    norm_num [correctPosterior, learnStep]
  refine ⟨h1, by norm_num [learnStep], h2, ?_⟩
  rw [h1, h2]
  norm_num

/-- No forgetting: the learned state never transitions to unlearned, and a student known to have
learned (`p = 1`) stays learned after either response. -/
private theorem test_no_forgetting :
    (bkt (1 / 4) (1 / 5) (1 / 4) (1 / 10)).trans true false = 0 ∧
      learnedNextPrior 1 (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i1 i15 i14 i110) true = 1 ∧
      learnedNextPrior 1 (1 / 5) (1 / 4) (1 / 10) (normalized_bkt i1 i15 i14 i110) false = 1 := by
  refine ⟨by simp [bkt], ?_, ?_⟩
  · rw [((filter_formulas i1 i15 i14 i110).1 (by norm_num)).2]
    norm_num [correctPosterior, learnStep]
  · rw [((filter_formulas i1 i15 i14 i110).2 (by norm_num)).2]
    norm_num [incorrectPosterior, learnStep]

/-- Uninformative responses `g = 1 - s` (`g = 1/4, s = 3/4`): both posteriors equal the prior
`1/4`, and both learning-updated priors are `2/5`. -/
private theorem test_guess_eq_one_sub_slip :
    learnedPosterior (1 / 4) (1 / 5) (1 / 4) (3 / 4) (normalized_bkt i14 i15 i14 i34) true =
        1 / 4 ∧
      learnedPosterior (1 / 4) (1 / 5) (1 / 4) (3 / 4) (normalized_bkt i14 i15 i14 i34) false =
        1 / 4 ∧
      learnedNextPrior (1 / 4) (1 / 5) (1 / 4) (3 / 4) (normalized_bkt i14 i15 i14 i34) true =
        2 / 5 ∧
      learnedNextPrior (1 / 4) (1 / 5) (1 / 4) (3 / 4) (normalized_bkt i14 i15 i14 i34) false =
        2 / 5 := by
  have hc := (filter_formulas i14 i15 i14 i34).1 (by norm_num)
  have hi := (filter_formulas i14 i15 i14 i34).2 (by norm_num)
  rw [hc.1, hi.1, hc.2, hi.2]
  norm_num [correctPosterior, incorrectPosterior, learnStep]

/-- `L = 0`: the next prior equals the posterior (`6/11`); `L = 1`: the next prior is `1`. -/
private theorem test_learn_zero_one :
    learnedNextPrior (1 / 4) 0 (1 / 4) (1 / 10) (normalized_bkt i14 i0 i14 i110) true = 6 / 11 ∧
      learnedNextPrior (1 / 4) 1 (1 / 4) (1 / 10) (normalized_bkt i14 i1 i14 i110) true = 1 ∧
      learnedNextPrior (1 / 4) 1 (1 / 4) (1 / 10) (normalized_bkt i14 i1 i14 i110) false = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [((filter_formulas i14 i0 i14 i110).1 (by norm_num)).2]
    norm_num [correctPosterior, learnStep]
  · rw [((filter_formulas i14 i1 i14 i110).1 (by norm_num)).2]
    norm_num [correctPosterior, learnStep]
  · rw [((filter_formulas i14 i1 i14 i110).2 (by norm_num)).2]
    norm_num [incorrectPosterior, learnStep]

/-- Zero evidence `p = g = 0` for a correct response: the evidence is `0` (so the guard of
`filter_formulas` fails), the totalized closed forms of both state posteriors are `0 / 0 = 0`,
while the filter posterior at that word is still a probability distribution over paths, so the
positivity guard cannot be dropped. -/
private theorem test_zero_evidence_correct :
    likelihood (bkt 0 (1 / 5) 0 (1 / 10)) (extend 0 (fun _ => true)) 0 = 0 ∧
      ¬ (0 < (0 : ℝ) * (1 - 1 / 10) + (1 - 0) * 0) ∧
      correctPosterior 0 0 (1 / 10) = 0 ∧
      (1 - 0 : ℝ) * 0 / (0 * (1 - 1 / 10) + (1 - 0) * 0) = 0 ∧
      ∑ z : Fin 1 → Bool,
        (filterPosterior (bkt 0 (1 / 5) 0 (1 / 10)) (normalized_bkt i0 i15 i0 i110) 0
          (fun _ => true) {z}).toReal = 1 := by
  refine ⟨?_, by norm_num, by norm_num [correctPosterior], by norm_num, ?_⟩
  · rw [likelihood_response]
    norm_num
  · have key : ∀ μ : MeasureTheory.Measure (Fin 1 → Bool),
        MeasureTheory.IsProbabilityMeasure μ →
        ∑ z : Fin 1 → Bool, (μ {z}).toReal = 1 := by
      intro μ hM
      have hfin : ∀ z : Fin 1 → Bool, μ {z} ≠ ⊤ := by
        intro z
        have hle : μ {z} ≤ 1 := by
          have h := MeasureTheory.measure_mono (μ := μ)
            (Set.subset_univ ({z} : Set (Fin 1 → Bool)))
          rwa [hM.measure_univ] at h
        exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
      have hsum : ∑ z : Fin 1 → Bool, μ {z} = 1 := by
        simp [hM.measure_univ]
      have h2 : (∑ z : Fin 1 → Bool, μ {z}).toReal
          = ∑ z : Fin 1 → Bool, (μ {z}).toReal :=
        ENNReal.toReal_sum (fun z _ => hfin z)
      rw [← h2, hsum]
      simp
    have hK : ProbabilityTheory.IsMarkovKernel (filterPosterior (bkt 0 (1 / 5) 0 (1 / 10))
        (normalized_bkt i0 i15 i0 i110) 0) := by
      unfold filterPosterior
      infer_instance
    exact key _ (hK.isProbabilityMeasure _)

/-- The no-forgetting instance is normalized but never `BaumWelch.Valid`: its transition
`true → false` is `0`. -/
private theorem test_not_valid (p L g s : ℝ) :
    ¬ Cslib.MachineLearning.Sequence.BaumWelch.Valid (bkt p L g s) := by
  intro hV
  have := hV.trans_pos true false
  simp [bkt] at this

end Cslib.MachineLearning.Sequence.KnowledgeTracing

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkovFilter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bayesian knowledge tracing as a no-forgetting HMM

Bayesian knowledge tracing is the two-state hidden Markov model whose
hidden state records whether a skill has been learned. This file
defines that model with initial learned probability `p`, learning
probability `L`, guess probability `g`, and slip probability `s`, all
allowed to take boundary values in `[0, 1]`.

The main theorem, `filter_formulas`, derives the standard posterior
and learning-update formulas after one response from the general HMM
filter and prediction correspondence. Each response is emitted from
the current state before the learning transition, and the learned
state never transitions back to unlearned.
-/

@[expose] public section

namespace Cslib.MachineLearning.Sequence.KnowledgeTracing

open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.Sequence.HiddenMarkovLaw
open Cslib.MachineLearning.Sequence.HiddenMarkovFilter

/-- Bayesian knowledge tracing (Corbett and Anderson, *Knowledge tracing: Modeling the
acquisition of procedural knowledge*, UMUAI 4, 1995) as a two-state HMM. The hidden state is
`true` when the skill is learned, the observation is `true` for a correct response. The initial
learned probability is `p`, an unlearned student learns with probability `L` at each step, a
learned student never forgets, an unlearned student guesses correctly with probability `g`, and a
learned student slips with probability `s`. Each response is emitted from the current state
before the learning transition. -/
noncomputable def bkt (p L g s : ℝ) : HMM Bool Bool ℝ where
  init k := if k then p else 1 - p
  trans k k' := if k then (if k' then 1 else 0) else (if k' then L else 1 - L)
  emit k r := if k then (if r then 1 - s else s) else (if r then g else 1 - g)

/-- The posterior learned probability after a correct response, under positive
evidence: `p (1 - s) / (p (1 - s) + (1 - p) g)`. At zero evidence Lean's
totalized division (`x / 0 = 0`) gives `0`; that value is not a posterior
probability. -/
noncomputable def correctPosterior (p g s : ℝ) : ℝ :=
  p * (1 - s) / (p * (1 - s) + (1 - p) * g)

/-- The posterior learned probability after an incorrect response, under
positive evidence: `p s / (p s + (1 - p) (1 - g))`. At zero evidence
Lean's totalized division (`x / 0 = 0`) gives `0`; that value is not a
posterior probability. -/
noncomputable def incorrectPosterior (p g s : ℝ) : ℝ :=
  p * s / (p * s + (1 - p) * (1 - g))

/-- The learning update of a learned probability `q`: an unlearned student learns with
probability `L` and a learned one never forgets, giving `q + (1 - q) L`. -/
def learnStep (L q : ℝ) : ℝ :=
  q + (1 - q) * L

/-- With all four parameters in `[0, 1]`, the knowledge-tracing HMM is normalized. -/
theorem normalized_bkt {p L g s : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hL : L ∈ Set.Icc (0 : ℝ) 1)
    (hg : g ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) : Normalized (bkt p L g s) := by
  obtain ⟨hp0, hp1⟩ := Set.mem_Icc.mp hp
  obtain ⟨hL0, hL1⟩ := Set.mem_Icc.mp hL
  obtain ⟨hg0, hg1⟩ := Set.mem_Icc.mp hg
  obtain ⟨hs0, hs1⟩ := Set.mem_Icc.mp hs
  refine ⟨fun k => by cases k <;> simp [bkt] <;> linarith, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bkt]
  · intro k k'; cases k <;> cases k' <;> simp [bkt] <;> linarith
  · intro k; cases k <;> simp [bkt]
  · intro k r; cases k <;> cases r <;> simp [bkt] <;> linarith
  · intro k; cases k <;> simp [bkt]

/-- The posterior probability that the skill is learned at time `0` given the first response
`r`: the filter posterior mass of the paths whose state at time `0` is `true`. -/
noncomputable def learnedPosterior (p L g s : ℝ) (hN : Normalized (bkt p L g s)) (r : Bool) :
    ℝ :=
  ∑ z ∈ Finset.univ.filter (fun z : Fin 1 → Bool => z (Fin.last 0) = true),
    (filterPosterior (bkt p L g s) hN 0 (fun _ => r) {z}).toReal

/-- The learned probability at time `1` given the first response `r`: the one-step predictive
posterior mass of the paths whose state at time `1` is `true`. -/
noncomputable def learnedNextPrior (p L g s : ℝ) (hN : Normalized (bkt p L g s)) (r : Bool) :
    ℝ :=
  ∑ z ∈ Finset.univ.filter (fun z : Fin 2 → Bool => z (Fin.last 1) = true),
    (predictivePosterior (bkt p L g s) hN 0 (fun _ => r) {z}).toReal

/-- The evidence of a single response: `p (1 - s) + (1 - p) g` for a correct response and
`p s + (1 - p) (1 - g)` for an incorrect one. -/
theorem likelihood_response (p L g s : ℝ) (r : Bool) :
    likelihood (bkt p L g s) (extend 0 (fun _ => r)) 0 =
      if r then p * (1 - s) + (1 - p) * g else p * s + (1 - p) * (1 - g) := by
  have hx0 : extend 0 (fun _ => r) 0 = r := by simp [extend]
  have sum_bool_paths : ∀ F : (Fin (0 + 1) → Bool) → ℝ,
      ∑ z, F z = ∑ b : Bool, F (fun _ => b) := by
    intro F
    let e : Bool ≃ (Fin (0 + 1) → Bool) :=
      ⟨fun b _ => b, fun z => z 0, fun b => rfl, fun z => funext fun i => by
        have hi := i.isLt
        have h0i : (0 : Fin (0 + 1)) = i := by
          ext
          simp
        exact congrArg z h0i⟩
    exact (e.sum_comp F).symm
  simp only [likelihood, pathProb]
  rw [sum_bool_paths, hx0]
  cases r <;> simp [bkt]

/-- **Knowledge-tracing filter formulas.** For parameters in `[0, 1]` and a response of positive
probability, the posterior learned probability after the response and the learning-updated
learned probability for the next step are the standard knowledge-tracing formulas: after a correct
response `correctPosterior p g s` and `learnStep L (correctPosterior p g s)`, after an incorrect
response `incorrectPosterior p g s` and `learnStep L (incorrectPosterior p g s)`. -/
theorem filter_formulas {p L g s : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hL : L ∈ Set.Icc (0 : ℝ) 1) (hg : g ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (0 < p * (1 - s) + (1 - p) * g →
      learnedPosterior p L g s (normalized_bkt hp hL hg hs) true = correctPosterior p g s ∧
      learnedNextPrior p L g s (normalized_bkt hp hL hg hs) true =
        learnStep L (correctPosterior p g s)) ∧
    (0 < p * s + (1 - p) * (1 - g) →
      learnedPosterior p L g s (normalized_bkt hp hL hg hs) false = incorrectPosterior p g s ∧
      learnedNextPrior p L g s (normalized_bkt hp hL hg hs) false =
        learnStep L (incorrectPosterior p g s)) := by
  constructor
  · intro hpos
    have hE : p * (1 - s) + (1 - p) * g ≠ 0 := ne_of_gt hpos
    have hx : 0 < likelihood (bkt p L g s) (extend 0 (fun _ => true)) 0 := by
      simpa [likelihood_response] using hpos
    have hb := posterior_prediction_match (bkt p L g s) (normalized_bkt hp hL hg hs) 0
      (fun _ => true) hx
    have hx0 : extend 0 (fun _ => true) 0 = true := by simp [extend]
    have hLk : likelihood (bkt p L g s) (extend 0 (fun _ => true)) (0 + 0)
        = p * (1 - s) + (1 - p) * g := by
      simpa using likelihood_response p L g s true
    have hFt : forward (bkt p L g s) (extend 0 (fun _ => true)) 0 true = p * (1 - s) := by
      simp [forward, hx0, bkt]
    have hFf : forward (bkt p L g s) (extend 0 (fun _ => true)) 0 false = (1 - p) * g := by
      simp [forward, hx0, bkt]
    have hBt : backward (bkt p L g s) (extend 0 (fun _ => true)) 0 0 true = 1 := by
      simp [backward]
    have hBf : backward (bkt p L g s) (extend 0 (fun _ => true)) 0 0 false = 1 := by
      simp [backward]
    have hSt : smoothed (extend 0 (fun _ => true)) (bkt p L g s) 0 0 true
        = correctPosterior p g s := by
      simp only [smoothed, hFt, hBt, hLk, correctPosterior]
      ring
    have hSf : smoothed (extend 0 (fun _ => true)) (bkt p L g s) 0 0 false
        = (1 - p) * g / (p * (1 - s) + (1 - p) * g) := by
      simp only [smoothed, hFf, hBf, hLk]
      ring
    have hS : ∀ k : Bool, smoothed (extend 0 (fun _ => true)) (bkt p L g s) 0 0 k
        = if k then correctPosterior p g s
          else (1 - p) * g / (p * (1 - s) + (1 - p) * g) := by
      intro k
      cases k <;> simp [hSt, hSf]
    have hPr : prediction (extend 0 (fun _ => true)) (bkt p L g s) 0 true
        = learnStep L (correctPosterior p g s) := by
      simp only [prediction, hS]
      simp [bkt, learnStep, correctPosterior]
      field_simp [hE]
      simp
    constructor
    · rw [learnedPosterior, ← hb.1 true, hSt]
    · rw [learnedNextPrior, ← hb.2 true, hPr]
  · intro hpos
    have hE : p * s + (1 - p) * (1 - g) ≠ 0 := ne_of_gt hpos
    have hx : 0 < likelihood (bkt p L g s) (extend 0 (fun _ => false)) 0 := by
      simpa [likelihood_response] using hpos
    have hb := posterior_prediction_match (bkt p L g s) (normalized_bkt hp hL hg hs) 0
      (fun _ => false) hx
    have hx0 : extend 0 (fun _ => false) 0 = false := by simp [extend]
    have hLk : likelihood (bkt p L g s) (extend 0 (fun _ => false)) (0 + 0)
        = p * s + (1 - p) * (1 - g) := by
      simpa using likelihood_response p L g s false
    have hFt : forward (bkt p L g s) (extend 0 (fun _ => false)) 0 true = p * s := by
      simp [forward, hx0, bkt]
    have hFf : forward (bkt p L g s) (extend 0 (fun _ => false)) 0 false
        = (1 - p) * (1 - g) := by
      simp [forward, hx0, bkt]
    have hBt : backward (bkt p L g s) (extend 0 (fun _ => false)) 0 0 true = 1 := by
      simp [backward]
    have hBf : backward (bkt p L g s) (extend 0 (fun _ => false)) 0 0 false = 1 := by
      simp [backward]
    have hSt : smoothed (extend 0 (fun _ => false)) (bkt p L g s) 0 0 true
        = incorrectPosterior p g s := by
      simp only [smoothed, hFt, hBt, hLk, incorrectPosterior]
      ring
    have hSf : smoothed (extend 0 (fun _ => false)) (bkt p L g s) 0 0 false
        = (1 - p) * (1 - g) / (p * s + (1 - p) * (1 - g)) := by
      simp only [smoothed, hFf, hBf, hLk]
      ring
    have hS : ∀ k : Bool, smoothed (extend 0 (fun _ => false)) (bkt p L g s) 0 0 k
        = if k then incorrectPosterior p g s
          else (1 - p) * (1 - g) / (p * s + (1 - p) * (1 - g)) := by
      intro k
      cases k <;> simp [hSt, hSf]
    have hPr : prediction (extend 0 (fun _ => false)) (bkt p L g s) 0 true
        = learnStep L (incorrectPosterior p g s) := by
      simp only [prediction, hS]
      simp [bkt, learnStep, incorrectPosterior]
      field_simp [hE]
      simp
    constructor
    · rw [learnedPosterior, ← hb.1 true, hSt]
    · rw [learnedNextPrior, ← hb.2 true, hPr]
end Cslib.MachineLearning.Sequence.KnowledgeTracing

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.GenerativeModel
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.NormNum

/-! # Regressions for the finite generative-model bound -/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Lean.MDP.GenerativeModel

open Cslib.Algorithms.Lean.MarkovDecision Cslib.Algorithms.Lean.MarkovDecision.Simplex
open MeasureTheory ProbabilityTheory

private def model : MDP (Fin 2) Unit ℝ where
  reward s _ := if s = 1 then 1 else 0
  prob _ _ y := if y = 1 then 1 else 0

private theorem model_stochastic : model.Stochastic := by
  constructor
  · intro s a y
    simp only [model]
    split <;> norm_num
  · intro s a
    simp [model]

-- One row has two copies of state 0 and one of state 1; the other row always visits state 1.
private def samples (s : Fin 2) (_ : Unit) (i : Fin 3) : Fin 2 :=
  if s = 0 then (if i = 2 then 1 else 0) else 1

private theorem sample_frequencies : (empiricalMDP model samples).prob 0 () 0 = 2 / 3 ∧
    (empiricalMDP model samples).prob 0 () 1 = 1 / 3 ∧
    (empiricalMDP model samples).prob 1 () 0 = 0 ∧
    (empiricalMDP model samples).prob 1 () 1 = 1 := by
  norm_num [empiricalMDP, empFreq, samples, Finset.natCast_card_filter, Fin.sum_univ_three]

-- With zero discount the original and empirical optimal action values coincide even when a
-- transition changes. The row error of the first row is 4/3, and the other row is exact.
example :
    let M' := empiricalMDP model samples
    let hM' := empiricalMDP_stochastic model samples (by decide)
    qValue model 0 (optimalValue model 0 model_stochastic le_rfl zero_lt_one) 0 () =
      qValue M' 0 (optimalValue M' 0 hM' le_rfl zero_lt_one) 0 () := by
  intro M' hM'
  have hrow (s : Fin 2) (a : Unit) : ∑ y, |model.prob s a y - M'.prob s a y| ≤ 4 / 3 := by
    cases a
    have hs : s = 0 ∨ s = 1 := by fin_cases s <;> decide
    rcases hs with rfl | rfl
    · change (∑ y, |model.prob 0 () y - (empiricalMDP model samples).prob 0 () y|) ≤ 4 / 3
      rw [Fin.sum_univ_two, sample_frequencies.1, sample_frequencies.2.1]
      norm_num [model]
    · change (∑ y, |model.prob 1 () y - (empiricalMDP model samples).prob 1 () y|) ≤ 4 / 3
      rw [Fin.sum_univ_two, sample_frequencies.2.2.1, sample_frequencies.2.2.2]
      norm_num [model]
  have h := abs_optimalQ_sub_optimalQ_le model_stochastic hM' le_rfl zero_lt_one rfl
    (fun s a => by simp only [model]; split <;> norm_num) hrow 0 ()
  simp only [zero_mul, zero_div] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

-- At positive discount the first row change affects future rewards: Q*(0, ()) falls
-- from 1 to 1/2, while the absorbing state's value stays 2.
example (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    let M' := empiricalMDP model samples
    let hM' := empiricalMDP_stochastic model samples (by decide)
    qValue model (1 / 2) (optimalValue model (1 / 2) model_stochastic h₀ h₁) 0 () -
      qValue M' (1 / 2) (optimalValue M' (1 / 2) hM' h₀ h₁) 0 () = 1 / 2 := by
  intro M' hM'
  let V : Fin 2 → ℝ := fun s => if s = 1 then 2 else 1
  let V' : Fin 2 → ℝ := fun s => if s = 1 then 2 else 1 / 2
  have hV : V = optimalValue model (1 / 2) model_stochastic h₀ h₁ := by
    apply eq_optimalValue_of_bellman_eq
    funext s
    rw [show bellman model (1 / 2) V s = qValue model (1 / 2) V s () by
      simp [bellman]]
    by_cases hs : s = 1 <;> norm_num [qValue, model, V, Fin.sum_univ_two, hs]
  have hV' : V' = optimalValue M' (1 / 2) hM' h₀ h₁ := by
    apply eq_optimalValue_of_bellman_eq
    funext s
    rw [show bellman M' (1 / 2) V' s = qValue M' (1 / 2) V' s () by
      simp [bellman]]
    have hs : s = 0 ∨ s = 1 := by fin_cases s <;> decide
    rcases hs with rfl | rfl
    · change model.reward 0 () + (1 / 2) *
        ∑ y, (empiricalMDP model samples).prob 0 () y * V' y = V' 0
      rw [Fin.sum_univ_two, sample_frequencies.1, sample_frequencies.2.1]
      norm_num [model, V']
    · change model.reward 1 () + (1 / 2) *
        ∑ y, (empiricalMDP model samples).prob 1 () y * V' y = V' 1
      rw [Fin.sum_univ_two, sample_frequencies.2.2.1, sample_frequencies.2.2.2]
      norm_num [model, V']
  rw [← hV, ← hV']
  change qValue model (1 / 2) V 0 () - (model.reward 0 () + (1 / 2) *
      ∑ y, (empiricalMDP model samples).prob 0 () y * V' y) = 1 / 2
  rw [Fin.sum_univ_two, sample_frequencies.1, sample_frequencies.2.1]
  norm_num [qValue, model, V, V', Fin.sum_univ_two]

private def oneState : MDP Unit Unit ℝ where
  reward _ _ := 0
  prob _ _ _ := 1

private theorem oneState_stochastic : oneState.Stochastic := by
  constructor <;> simp [oneState]

-- Instantiate the simultaneous guarantee on a point-mass experiment. With η = 2 and δ = 1/2,
-- the sufficient threshold is at most one sample, since log 2 ≤ 1.
example : 1 - (1 / 2 : ℝ) ≤ (Measure.dirac () : Measure Unit).real {ω |
    let x : Unit → Unit → Fin 1 → Unit := fun _ _ _ => ω
    let M' := empiricalMDP oneState x
    let hM' := empiricalMDP_stochastic oneState x (by decide)
    (∀ s a, ∑ y, |M'.prob s a y - oneState.prob s a y| ≤ 2) ∧
    ∀ s a, |qValue M' 0 (optimalValue M' 0 hM' le_rfl zero_lt_one) s a -
      qValue oneState 0 (optimalValue oneState 0 oneState_stochastic le_rfl zero_lt_one) s a| ≤
        0 * 2 / (1 - 0) ^ 2} := by
  have hp (s a : Unit) (_ : Fin 1) (y : Unit) :
      (Measure.dirac () : Measure Unit).real ((id : Unit → Unit) ⁻¹' {y}) =
        oneState.prob s a y := by
    cases y
    have h : {()} = (Set.univ : Set Unit) := by ext ω; cases ω; simp
    simp [h, oneState]
  apply measureReal_empiricalMDP_accurate oneState oneState_stochastic (fun _ _ _ ω => ω)
    (fun _ _ _ => measurable_id) (fun _ _ => iIndepFun.of_subsingleton)
    hp (by decide) le_rfl zero_lt_one
    (fun _ _ => by simp [oneState]) (by norm_num) (by norm_num)
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  linarith

end CSLibExtTest.Algorithms.Lean.MDP.GenerativeModel

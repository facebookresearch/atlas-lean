/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

import Mathlib.MeasureTheory.Integral.Bochner.Set
import MathlibExt.Probability.HoeffdingBernoulliSumAbsTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Monte Carlo estimation of a limit-state failure probability -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Reliability

/-- **Monte Carlo estimate of a failure probability.** For `n > 0` independent samples with
identical distributions, and a measurable real limit-state function `g`, count a failure
when `g ≤ 0`, including equality. The probability of absolute error greater than `ε > 0`
for the sample mean of the failure indicators is at most `2 * exp (-2 * ε^2 * n)`.
For `0 < δ < 1`, sampling at least `log (2 / δ) / (2 * ε^2)` times bounds that probability
by `δ`. This is absolute-error control, not relative-error control for rare failures.
The bound uses Hoeffding's inequality (W. Hoeffding, *Probability inequalities for sums of
bounded random variables*, JASA 58 (1963), 13–30, Theorem 2). -/
theorem monte_carlo_failure_probability {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → S)
    (hind : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X ⟨0, hn⟩) P P)
    (g : S → ℝ) (hg : Measurable g) {ε : ℝ} (hε : 0 < ε) :
    let s := {z | g z ≤ 0}
    let p := P.real (X ⟨0, hn⟩ ⁻¹' s)
    let estimate := fun ω => (∑ i, s.indicator (fun _ => (1 : ℝ)) (X i ω)) / (n : ℝ)
    let bad := {ω | ε < |estimate ω - p|}
    P.real bad ≤ 2 * Real.exp (-2 * ε ^ 2 * (n : ℝ)) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → Real.log (2 / δ) / (2 * ε ^ 2) ≤ (n : ℝ) → P.real bad ≤ δ := by
  classical
  intro s p estimate bad
  let f : S → ℝ := s.indicator (fun _ => 1)
  let B : Fin n → Ω → ℝ := fun i => f ∘ X i
  have hs : MeasurableSet s := measurableSet_le hg measurable_const
  have hf : Measurable f := measurable_const.indicator hs
  have hBmeas (i : Fin n) : AEMeasurable (B i) P :=
    hf.comp_aemeasurable (hident i).aemeasurable_fst
  have hBval (i : Fin n) : ∀ᵐ ω ∂P, B i ω = 0 ∨ B i ω = 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    by_cases h : X i ω ∈ s
    · right
      simp [B, f, Set.indicator_of_mem h]
    · left
      simp [B, f, Set.indicator_of_notMem h]
  have hBmean (i : Fin n) : (∫ ω, B i ω ∂P) = p := by
    change (∫ ω, (f ∘ X i) ω ∂P) = p
    rw [((hident i).comp hf).integral_eq]
    have hmeas := (hident ⟨0, hn⟩).aemeasurable_fst
    calc
      (∫ ω, (f ∘ X ⟨0, hn⟩) ω ∂P) = ∫ z, f z ∂P.map (X ⟨0, hn⟩) :=
        (integral_map hmeas hf.aestronglyMeasurable).symm
      _ = p := by
        change (∫ z, s.indicator (1 : S → ℝ) z ∂P.map (X ⟨0, hn⟩)) = p
        rw [integral_indicator_one hs]
        simp only [p, measureReal_def, Measure.map_apply_of_aemeasurable hmeas hs]
  have htail := hoeffding_bernoulli_sum_abs_tail B p ε (hind.comp (fun _ => f) (fun _ => hf))
    hBmeas hBval hBmean hε
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsub : bad = {ω | ε * (n : ℝ) < |(∑ i, B i ω) - (n : ℝ) * p|} := by
    ext ω
    change (ε < |(∑ i, B i ω) / (n : ℝ) - p|) ↔
      ε * (n : ℝ) < |(∑ i, B i ω) - (n : ℝ) * p|
    have hdiv : (∑ i, B i ω) / (n : ℝ) - p = ((∑ i, B i ω) - (n : ℝ) * p) / (n : ℝ) := by
      field_simp [hnR.ne']
    rw [hdiv, abs_div, abs_of_pos hnR, lt_div_iff₀ hnR]
  rw [← hsub] at htail
  refine ⟨htail, ?_⟩
  intro δ hδ _ hsize
  have hden : 0 < 2 * ε ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hε)
  have hlog : Real.log (2 / δ) ≤ 2 * ε ^ 2 * (n : ℝ) := by
    simpa only [mul_comm (n : ℝ)] using (div_le_iff₀ hden).mp hsize
  have hexp : Real.exp (-2 * ε ^ 2 * (n : ℝ)) ≤ Real.exp (-Real.log (2 / δ)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hδ)] at hexp
  calc
    P.real bad ≤ 2 * Real.exp (-2 * ε ^ 2 * (n : ℝ)) := htail
    _ ≤ 2 * (2 / δ)⁻¹ := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = δ := by field_simp [hδ.ne']

end Reliability

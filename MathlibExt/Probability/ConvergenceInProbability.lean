/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.Normed.Group.Real

@[expose] public section

section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace MathlibExt.Probability.ConvergenceInProbability

/-!
# Convergence in probability and subsequential almost-everywhere convergence

For real-valued random variables on a finite measure space, convergence in
probability (in the textbook sense: `μ {|Xₙ - Y| > ε} → 0` for every `ε > 0`)
holds if and only if every subsequence of `Xₙ` admits a further subsequence
converging to `Y` almost everywhere.

## Main results

- `tendstoInMeasure_iff_tendsto_measure_abs_sub`: Mathlib's `TendstoInMeasure`
  unfolded into the textbook `ε`-formulation above. Mathlib states convergence
  in measure via `enorm`; this bridge lemma is the form used in the proof.
- `convergence_in_probability_iff_subsequential_ae_convergence`: the book's
  theorem (Lecture 9, "Convergence in probability subsequential a.s.
  convergence").
-/

/-- **Convergence in measure in the textbook `ε`-formulation.**

For real-valued functions, `TendstoInMeasure μ X atTop Y` holds if and only if
`μ {ω | ε < |X n ω - Y ω|} → 0` for every `ε > 0`. This is the definition of
convergence in probability used in the book; Mathlib's definition is stated
via `enorm` instead. -/
theorem tendstoInMeasure_iff_tendsto_measure_abs_sub
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} :
    TendstoInMeasure μ X atTop Y ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => μ {ω | ε < |X n ω - Y ω|}) atTop (𝓝 0) := by
  constructor
  · intro hTIM ε hε
    have hε_ennreal : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    have hε_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
    have h := (tendstoInMeasure_iff_enorm.mp hTIM) (ENNReal.ofReal ε) hε_ennreal hε_ne_top
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    · intro n; exact zero_le
    · intro n
      apply measure_mono
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
  · intro hconv
    rw [tendstoInMeasure_iff_enorm]
    intro ε hε hε_top
    set δ := ε.toReal with hδ
    have hδ_pos : 0 < δ := ENNReal.toReal_pos hε.ne' hε_top
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hconv (δ / 2) (half_pos hδ_pos))
    · intro n; exact zero_le
    · intro n
      apply measure_mono
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [Real.enorm_eq_ofReal_abs] at hω
      have h1 : δ ≤ |X n ω - Y ω| :=
        ENNReal.toReal_le_of_le_ofReal (abs_nonneg _) hω
      linarith

/-- **Convergence in probability via subsequential a.s. convergence** (Lecture 9).

For real random variables `Xₙ`, `Y` on a finite measure space, `Xₙ → Y` in
probability (i.e. `μ {|Xₙ - Y| > ε} → 0` for every `ε > 0`) if and only if
every subsequence of `Xₙ` admits a further subsequence converging to `Y`
almost everywhere. -/
theorem convergence_in_probability_iff_subsequential_ae_convergence
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε < |X n ω - Y ω|}) atTop (𝓝 0)) ↔
    (∀ ns : ℕ → ℕ, StrictMono ns →
      ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ ω ∂μ, Tendsto (fun k => X (ns (ns' k)) ω) atTop (𝓝 (Y ω))) := by
  rw [← tendstoInMeasure_iff_tendsto_measure_abs_sub]
  exact exists_seq_tendstoInMeasure_atTop_iff hX

end MathlibExt.Probability.ConvergenceInProbability

end

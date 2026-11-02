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

/-- **Convergence in measure in the textbook ε-formulation.** Let $\mu$ be a measure on a
measurable space $\Omega$, and let $X_n : \Omega \to \mathbb{R}$ ($n \in \mathbb{N}$) and
$Y : \Omega \to \mathbb{R}$ be functions. Then $X_n$ converges to $Y$ in $\mu$-measure, that is,
$\mu(\{\omega : |X_n(\omega) - Y(\omega)| \ge \varepsilon\}) \to 0$ as $n \to \infty$ for every
$\varepsilon \in (0, \infty]$, if and only if
$\mu(\{\omega : |X_n(\omega) - Y(\omega)| > \varepsilon\}) \to 0$ as $n \to \infty$ for every
real $\varepsilon > 0$.

The second condition is the definition of convergence in probability used in the book. -/
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

/-- **Convergence in probability via subsequential a.s. convergence.** Let $\mu$ be a finite
measure on a measurable space $\Omega$, let $X_n : \Omega \to \mathbb{R}$ ($n \in \mathbb{N}$) be
$\mu$-almost everywhere strongly measurable functions, and let $Y : \Omega \to \mathbb{R}$ be any
function. Then $\mu(\{\omega : |X_n(\omega) - Y(\omega)| > \varepsilon\}) \to 0$ as
$n \to \infty$ for every real $\varepsilon > 0$ if and only if for every strictly increasing
sequence $(n_k)$ of natural numbers there is a strictly increasing sequence $(k_j)$ of natural
numbers such that $X_{n_{k_j}}(\omega) \to Y(\omega)$ as $j \to \infty$ for $\mu$-almost every
$\omega \in \Omega$.

Source: Lecture 9, convergence in probability via subsequential a.s. convergence. -/
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

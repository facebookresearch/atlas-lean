/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Independence.Basic

/-!
# Tail probabilities in Kolmogorov's three-series theorem

The first of the three series in Kolmogorov's three-series theorem
(Lecture 10): if the partial sums of an independent sequence converge
almost surely, then for every threshold `A > 0` the tail probabilities
`∑ₙ P(|Xₙ| > A)` form a convergent series.

Source: `v1/Atlas/TheoryOfProbability/targets.yaml`, target
"Theorem (Kolmogorov three-series theorem)"; v1 formalization:
`v1/Atlas/TheoryOfProbability/code/KolmogorovThreeSeries.lean`,
`KolmogorovThreeSeries.summable_tail_prob_of_ae_tendsto` (fully proved
there). The other two series of the necessity direction (summability of
the truncated means and variances) rest in v1 on
`summable_mean_and_variance_of_ae_tendsto_ax`, left unproved there, and
are NOT claimed here. The sufficiency direction is a separate import.
-/

public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Kolmogorov three-series theorem, necessity, first series.** Let $(X_n)_{n \ge 0}$ be a
sequence of independent measurable real random variables on a probability space
$(\Omega, \mu)$ whose partial sums converge almost surely: there is a function
$S : \Omega \to \mathbb{R}$ such that $\sum_{i < n} X_i(\omega) \to S(\omega)$ as $n \to \infty$
for $\mu$-almost every $\omega$. Then for every $A > 0$ the tail probabilities are summable:
$\sum_n \mu(\{\omega : |X_n(\omega)| > A\}) < \infty$.

Proof: argue by contradiction via the second Borel–Cantelli lemma. If the tail probabilities
summed to $\infty$, the events $\{|X_n| > A\}$ would occur infinitely often with probability
one; but almost-sure convergence of the partial sums forces $X_n \to 0$ almost surely, hence
eventually $|X_n| \le A$. -/
theorem summable_tail_prob_of_ae_tendsto [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) {A : ℝ} (hA : A > 0)
    (hX_tend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => X i ω)) atTop (nhds (S ω))) :
    (∑' n, μ {ω | A < |X n ω|}) < ⊤ := by
  by_contra h_not_fin
  push Not at h_not_fin
  have h_infty : (∑' n, μ {ω | A < |X n ω|}) = ⊤ := top_le_iff.mp h_not_fin
  have h_meas : ∀ n, MeasurableSet {ω | A < |X n ω|} := fun n =>
    measurableSet_lt measurable_const (hX_meas n).norm
  have h_indep : iIndepSet (fun n => {ω | A < |X n ω|}) μ := by
    rw [iIndepSet_iff_meas_biInter h_meas]
    intro S
    have h_eq : ∀ n, {ω : Ω | A < |X n ω|} = X n ⁻¹' {x : ℝ | A < |x|} := by
      intro n
      ext ω
      simp
    simp_rw [h_eq]
    exact hX_indep.measure_inter_preimage_eq_mul S
      (fun _ _ => measurableSet_lt measurable_const measurable_norm)
  have h_limsup : μ (limsup (fun n => {ω | A < |X n ω|}) atTop) = 1 :=
    measure_limsup_eq_one h_meas h_indep h_infty
  obtain ⟨S, hS⟩ := hX_tend
  have h_term_zero : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds 0) := by
    filter_upwards [hS] with ω hω
    have h1 : Tendsto (fun n => (∑ i ∈ Finset.range (n + 1), X i ω) -
        ∑ i ∈ Finset.range n, X i ω) atTop (nhds (S ω - S ω)) :=
      (hω.comp (tendsto_add_atTop_nat 1)).sub hω
    simp only [Finset.sum_range_succ_sub_sum, sub_self] at h1
    exact h1
  have h_ev_not_mem : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ {ω' | A < |X n ω'|} := by
    filter_upwards [h_term_zero] with ω hω
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hω) A hA
    exact eventually_atTop.mpr ⟨N, fun n hn => by
      simp only [not_lt]
      have hd := hN n hn
      rw [Real.dist_eq, sub_zero] at hd
      exact le_of_lt hd⟩
  have h_ae_not_limsup :
      ∀ᵐ ω ∂μ, ω ∉ limsup (fun n => {ω | A < |X n ω|}) atTop := by
    filter_upwards [h_ev_not_mem] with ω hω
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter,
      Set.mem_iUnion, not_forall, not_exists]
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    exact ⟨N, fun n hn => hN n (by omega)⟩
  have h_freq_zero : μ (limsup (fun n => {ω | A < |X n ω|}) atTop) = 0 := by
    rw [ae_iff] at h_ae_not_limsup
    simp only [not_not] at h_ae_not_limsup
    exact h_ae_not_limsup
  rw [h_freq_zero] at h_limsup
  exact absurd h_limsup (by norm_num)

/-- **Divergent tail probabilities prevent almost-sure convergence of partial sums.** Let
$(X_n)_{n \ge 0}$ be a sequence of independent measurable real random variables on a probability
space $(\Omega, \mu)$, and let $A > 0$. If $\sum_n \mu(\{\omega : |X_n(\omega)| > A\}) = \infty$,
then there is no function $S : \Omega \to \mathbb{R}$ such that, for $\mu$-almost every $\omega$,
the partial sums $\sum_{i < n} X_i(\omega)$ converge to $S(\omega)$ as $n \to \infty$. -/
theorem not_ae_tendsto_partial_sum_of_tsum_tail_prob_eq_top
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) {A : ℝ} (hA : A > 0)
    (hdiv : (∑' n, μ {ω | A < |X n ω|}) = ⊤) :
    ¬ ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => X i ω)) atTop (nhds (S ω)) := by
  intro hX_tend
  have hfin := summable_tail_prob_of_ae_tendsto hX_meas hX_indep hA hX_tend
  rw [hdiv] at hfin
  exact lt_irrefl (⊤ : ℝ≥0∞) hfin

end ProbabilityTheory

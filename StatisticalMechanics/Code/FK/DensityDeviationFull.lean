/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster
import Code.FK.FiniteEnergy
import Code.FK.DensityBounds
import Code.FK.ComparisonHolley
import Code.Inequalities.Pivotal

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]








noncomputable def fkMeanOpenCount (p q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), (chOpenCount G ω : ℝ) * fkProb G p q ω







omit [DecidableEq V] in


theorem chOpenCount_eq_sum_indicator (ω : ConfigSpace (Sym2 V)) :
    (chOpenCount G ω : ℝ)
      = ∑ e ∈ G.edgeFinset, (if ω e = true then (1 : ℝ) else 0) := by
  unfold chOpenCount
  rw [Finset.sum_boole]









theorem fkMeanOpenCount_eq_sum_marginals (p q : ℝ) :
    fkMeanOpenCount G p q = ∑ e ∈ G.edgeFinset, edgeMarginalOpen G p q e := by
  unfold fkMeanOpenCount edgeMarginalOpen
  
  have hexp : ∀ ω : ConfigSpace (Sym2 V),
      (chOpenCount G ω : ℝ) * fkProb G p q ω
        = ∑ e ∈ G.edgeFinset, (if ω e = true then fkProb G p q ω else 0) := by
    intro ω
    rw [chOpenCount_eq_sum_indicator G ω, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    split <;> ring
  simp_rw [hexp]
  
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_filter]








theorem fkMeanOpenCount_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    fkMeanOpenCount G p q ≤ p * (G.edgeFinset.card : ℝ) := by
  rw [fkMeanOpenCount_eq_sum_marginals G p q]
  calc ∑ e ∈ G.edgeFinset, edgeMarginalOpen G p q e
      ≤ ∑ _e ∈ G.edgeFinset, p := by
        apply Finset.sum_le_sum
        intro e he
        exact (edge_density_bounds G hp hp1 hq he).2
    _ = p * (G.edgeFinset.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]



theorem fkMeanOpenCount_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    p / (p + q * (1 - p)) * (G.edgeFinset.card : ℝ) ≤ fkMeanOpenCount G p q := by
  rw [fkMeanOpenCount_eq_sum_marginals G p q]
  calc p / (p + q * (1 - p)) * (G.edgeFinset.card : ℝ)
      = ∑ _e ∈ G.edgeFinset, p / (p + q * (1 - p)) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ e ∈ G.edgeFinset, edgeMarginalOpen G p q e := by
        apply Finset.sum_le_sum
        intro e he
        exact (edge_density_bounds G hp hp1 hq he).1


theorem fkMeanOpenCount_le_card {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkMeanOpenCount G p q ≤ (G.edgeFinset.card : ℝ) := by
  unfold fkMeanOpenCount
  calc ∑ ω : ConfigSpace (Sym2 V), (chOpenCount G ω : ℝ) * fkProb G p q ω
      ≤ ∑ ω : ConfigSpace (Sym2 V), (G.edgeFinset.card : ℝ) * fkProb G p q ω := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_right _ (fkProb_nonneg G hp hp1 hq ω)
        unfold chOpenCount; exact_mod_cast Finset.card_filter_le _ _
    _ = (G.edgeFinset.card : ℝ) := by
        rw [← Finset.mul_sum, fkProb_sum_eq_one G hp hp1 hq, mul_one]



















theorem reverse_markov_upper {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (hX0 : ∀ ω, 0 ≤ X ω) {M μ ε : ℝ}
    (hmean : ∑ ω, X ω * w ω ≤ μ * M)
    (hμ : 0 ≤ μ) (hε : 0 < ε) (hM : 0 < M) :
    ε / (μ + ε) ≤ ∑ ω ∈ Finset.univ.filter (fun ω => X ω ≤ (μ + ε) * M), w ω := by
  have hμε : 0 < μ + ε := by linarith
  set t := (μ + ε) * M with ht
  have htpos : 0 < t := by positivity
  have hkey : t * (∑ ω ∈ Finset.univ.filter (fun ω => ¬ X ω ≤ t), w ω)
      ≤ ∑ ω, X ω * w ω := by
    calc t * (∑ ω ∈ Finset.univ.filter (fun ω => ¬ X ω ≤ t), w ω)
          = ∑ ω ∈ Finset.univ.filter (fun ω => ¬ X ω ≤ t), t * w ω := by rw [Finset.mul_sum]
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => ¬ X ω ≤ t), X ω * w ω := by
          apply Finset.sum_le_sum
          intro ω hω
          simp only [Finset.mem_filter, not_le] at hω
          exact mul_le_mul_of_nonneg_right hω.2.le (hw ω)
      _ ≤ ∑ ω, X ω * w ω := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro ω _ _; exact mul_nonneg (hX0 ω) (hw ω)
  have hmassA : ∑ ω ∈ Finset.univ.filter (fun ω => ¬ X ω ≤ t), w ω ≤ μ / (μ + ε) := by
    have h1 : t * (∑ ω ∈ Finset.univ.filter (fun ω => ¬ X ω ≤ t), w ω) ≤ μ * M :=
      le_trans hkey hmean
    rw [ht] at h1
    rw [le_div_iff₀ hμε]
    nlinarith [h1]
  have hsplit : (∑ ω ∈ Finset.univ.filter (fun ω => X ω ≤ t), w ω)
      + (∑ ω ∈ Finset.univ.filter (fun ω => ¬ X ω ≤ t), w ω) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω => X ω ≤ t) w]; exact hsum
  have hcompl : ε / (μ + ε) + μ / (μ + ε) = 1 := by field_simp; ring
  linarith [hmassA, hsplit, hcompl]










theorem reverse_markov_lower {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) {M : ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (hXM : ∀ ω, X ω ≤ M) {ν ε : ℝ}
    (hmean : ν * M ≤ ∑ ω, X ω * w ω)
    (hν1 : ν ≤ 1) (hε : 0 < ε) (hM : 0 < M) :
    ε / (1 - ν + ε) ≤ ∑ ω ∈ Finset.univ.filter (fun ω => (ν - ε) * M ≤ X ω), w ω := by
  have hden : 0 < 1 - ν + ε := by linarith
  set t := (ν - ε) * M with ht
  have hsplit_sum : (∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), X ω * w ω)
      + (∑ ω ∈ Finset.univ.filter (fun ω => ¬ t ≤ X ω), X ω * w ω) = ∑ ω, X ω * w ω := by
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω => t ≤ X ω) (fun ω => X ω * w ω)]
  have hB : ∑ ω ∈ Finset.univ.filter (fun ω => ¬ t ≤ X ω), X ω * w ω
      ≤ t * (∑ ω ∈ Finset.univ.filter (fun ω => ¬ t ≤ X ω), w ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω hω
    simp only [Finset.mem_filter, not_le] at hω
    exact mul_le_mul_of_nonneg_right hω.2.le (hw ω)
  have hBc : ∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), X ω * w ω
      ≤ M * (∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), w ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    exact mul_le_mul_of_nonneg_right (hXM ω) (hw ω)
  set mB := ∑ ω ∈ Finset.univ.filter (fun ω => ¬ t ≤ X ω), w ω with hmB
  set mBc := ∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), w ω with hmBc
  have hmass1 : mBc + mB = 1 := by
    rw [hmBc, hmB, Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω => t ≤ X ω) w]
    exact hsum
  have hmean_ub : ∑ ω, X ω * w ω ≤ M * mBc + t * mB := by
    rw [← hsplit_sum]; linarith [hB, hBc]
  have hmBbound : mB ≤ (1 - ν) / (1 - ν + ε) := by
    have h1 : ν * M ≤ M * mBc + t * mB := le_trans hmean hmean_ub
    rw [ht] at h1
    have hmBc_eq : mBc = 1 - mB := by linarith [hmass1]
    rw [hmBc_eq] at h1
    rw [le_div_iff₀ hden]
    nlinarith [h1]
  show ε / (1 - ν + ε) ≤ mBc
  have hmBc_eq : mBc = 1 - mB := by linarith [hmass1]
  rw [hmBc_eq]
  have hcompl : ε / (1 - ν + ε) + (1 - ν) / (1 - ν + ε) = 1 := by field_simp; ring
  linarith [hmBbound, hcompl]








noncomputable def fkOpenCountLeProb (p q : ℝ) (s : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => (chOpenCount G ω : ℝ) ≤ s),
    fkProb G p q ω



noncomputable def fkOpenCountGeProb (p q : ℝ) (s : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => s ≤ (chOpenCount G ω : ℝ)),
    fkProb G p q ω











theorem den_openCount_upper_deviation {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε ≤ 1 - p)
    (hEpos : 0 < (G.edgeFinset.card : ℝ)) :
    ε ≤ fkOpenCountLeProb G p q ((p + ε) * (G.edgeFinset.card : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hpe1 : p + ε ≤ 1 := by linarith
  have hrm := reverse_markov_upper
      (fun ω : ConfigSpace (Sym2 V) => fkProb G p q ω)
      (fun ω => (chOpenCount G ω : ℝ))
      (fun ω => fkProb_nonneg G hp hp1 hq0 ω)
      (fkProb_sum_eq_one G hp hp1 hq0)
      (fun ω => by positivity)
      (M := (G.edgeFinset.card : ℝ)) (μ := p) (ε := ε)
      (fkMeanOpenCount_le G hp hp1 hq) hp.le hε hEpos
  
  have hε_le : ε ≤ ε / (p + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < p + ε)]
    nlinarith
  exact le_trans hε_le hrm











theorem den_openCount_lower_deviation {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ p / (p + q * (1 - p)))
    (hEpos : 0 < (G.edgeFinset.card : ℝ)) :
    ε ≤ fkOpenCountGeProb G p q
        ((p / (p + q * (1 - p)) - ε) * (G.edgeFinset.card : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set b := p / (p + q * (1 - p)) with hb
  have hden : 0 < p + q * (1 - p) := by nlinarith
  
  have hb_pos : 0 < b := by rw [hb]; positivity
  have hb_le_one : b ≤ 1 := by
    rw [hb, div_le_one hden]; nlinarith
  have hrm := reverse_markov_lower
      (fun ω : ConfigSpace (Sym2 V) => fkProb G p q ω)
      (fun ω => (chOpenCount G ω : ℝ))
      (M := (G.edgeFinset.card : ℝ))
      (fun ω => fkProb_nonneg G hp hp1 hq0 ω)
      (fkProb_sum_eq_one G hp hp1 hq0)
      (fun ω => by
        show (chOpenCount G ω : ℝ) ≤ (G.edgeFinset.card : ℝ)
        unfold chOpenCount; exact_mod_cast Finset.card_filter_le _ _)
      (ν := b) (ε := ε)
      (fkMeanOpenCount_ge G hp hp1 hq) hb_le_one hε hEpos
  
  have hε_le : ε ≤ ε / (1 - b + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - b + ε)]
    nlinarith
  exact le_trans hε_le hrm

end FK

end StatMech

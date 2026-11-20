/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.FK.DensityDeviationFull
import Code.FK.DensityFiniteToInfinite
import Code.FK.AvgDensityCollapse
import Code.FK.UniformBulkDeviation

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}










theorem ivd_innerEdgeLE_refl (n : ℕ) (eb : Sym2 (boxVerts d n)) :
    innerEdgeLE d (le_refl n) eb = eb := by
  unfold innerEdgeLE boxVertInclLE
  rw [show (fun x : boxVerts d n =>
        (⟨(x : Site d), box_mono d (le_refl n) x.2⟩ : boxVerts d n)) = id by funext x; rfl]
  rw [Sym2.map_id]; rfl













theorem ivd_freeMeanOpenCount_le (n : ℕ) {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p = a) :
    fkMeanOpenCount (boxGraph d n) p 2 ≤ a * ((boxGraph d n).edgeFinset.card : ℝ) := by
  rw [fkMeanOpenCount_eq_sum_marginals]
  calc ∑ e ∈ (boxGraph d n).edgeFinset, edgeMarginalOpen (boxGraph d n) p 2 e
      = ∑ e ∈ (boxGraph d n).edgeFinset, edgeMargProb (fkProb (boxGraph d n) p 2) e :=
        Finset.sum_congr rfl fun e _ => (edgeMargProb_fkProb (boxGraph d n) p 2 e).symm
    _ ≤ ∑ e ∈ (boxGraph d n).edgeFinset, a := by
        refine Finset.sum_le_sum fun e he => ?_
        have h1 := dfi_free_per_edge_le n n (le_refl n) e hp hp1
        rw [ivd_innerEdgeLE_refl n e] at h1
        rw [← hhom e he]; exact h1
    _ = a * ((boxGraph d n).edgeFinset.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]






theorem ivd_wiredMeanOpenCount_eq_sum_marginals (n : ℕ) (p : ℝ) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
        (chOpenCount (boxGraph d n) ω : ℝ)
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω)
      = ∑ e ∈ (boxGraph d n).edgeFinset,
          edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2) e := by
  have hexp : ∀ ω : ConfigSpace (Sym2 (boxVerts d n)),
      (chOpenCount (boxGraph d n) ω : ℝ)
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω
        = ∑ e ∈ (boxGraph d n).edgeFinset,
            (if ω e = true then wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω else 0) := by
    intro ω
    rw [chOpenCount_eq_sum_indicator (boxGraph d n) ω, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by split <;> ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold edgeMargProb
  exact (Finset.sum_congr rfl fun ω _ => by split <;> simp_all)








theorem ivd_wiredMeanOpenCount_ge (n : ℕ) {p b : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p = b) :
    b * ((boxGraph d n).edgeFinset.card : ℝ)
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (chOpenCount (boxGraph d n) ω : ℝ)
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  rw [ivd_wiredMeanOpenCount_eq_sum_marginals]
  calc b * ((boxGraph d n).edgeFinset.card : ℝ)
      = ∑ _e ∈ (boxGraph d n).edgeFinset, b := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ e ∈ (boxGraph d n).edgeFinset,
          edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2) e := by
        refine Finset.sum_le_sum fun e he => ?_
        have h1 := dfi_wired_per_edge_ge n n (le_refl n) e hp hp1
        rw [ivd_innerEdgeLE_refl n e] at h1
        rw [← hhom e he]; exact h1











noncomputable def ivd_wiredOpenCountGeProb (d n : ℕ) (p : ℝ) (s : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter
      (fun ω : ConfigSpace (Sym2 (boxVerts d n)) => s ≤ (chOpenCount (boxGraph d n) ω : ℝ)),
    wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω




















theorem den_openCount_upper_deviation_iv (n : ℕ) {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha0 : 0 ≤ a)
    (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p = a)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε ≤ 1 - a)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ε ≤ fkOpenCountLeProb (boxGraph d n) p 2 ((a + ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
  have hae1 : a + ε ≤ 1 := by linarith
  have hrm := reverse_markov_upper
      (fun ω : ConfigSpace (Sym2 (boxVerts d n)) => fkProb (boxGraph d n) p 2 ω)
      (fun ω => (chOpenCount (boxGraph d n) ω : ℝ))
      (fun ω => fkProb_nonneg (boxGraph d n) hp hp1 (by norm_num) ω)
      (fkProb_sum_eq_one (boxGraph d n) hp hp1 (by norm_num))
      (fun ω => by positivity)
      (M := ((boxGraph d n).edgeFinset.card : ℝ)) (μ := a) (ε := ε)
      (ivd_freeMeanOpenCount_le n hp hp1 hhom) ha0 hε hEpos
  have hε_le : ε ≤ ε / (a + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < a + ε)]
    nlinarith
  exact le_trans hε_le hrm















theorem den_openCount_lower_deviation_iv (n : ℕ) {p b : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hb1 : b ≤ 1)
    (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p = b)
    {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ b)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ε ≤ ivd_wiredOpenCountGeProb d n p ((b - ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
  have hrm := reverse_markov_lower
      (fun ω : ConfigSpace (Sym2 (boxVerts d n)) =>
        wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω)
      (fun ω => (chOpenCount (boxGraph d n) ω : ℝ))
      (M := ((boxGraph d n).edgeFinset.card : ℝ))
      (fun ω => wiredFkProb_nonneg (boxGraph d n) (boxBoundary d n) hp hp1 (by norm_num) ω)
      (wiredFkProb_sum_eq_one (boxGraph d n) (boxBoundary d n) hp hp1 (by norm_num))
      (fun ω => by
        change (chOpenCount (boxGraph d n) ω : ℝ) ≤ ((boxGraph d n).edgeFinset.card : ℝ)
        unfold chOpenCount; exact_mod_cast Finset.card_filter_le _ _)
      (ν := b) (ε := ε)
      (ivd_wiredMeanOpenCount_ge n hp hp1 hhom) hb1 hε hEpos
  have hε_le : ε ≤ ε / (1 - b + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - b + ε)]
    nlinarith
  exact le_trans hε_le hrm

















theorem ivd_freeEdgeDensity_nonneg (n : ℕ) (e : Sym2 (boxVerts d n)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) : 0 ≤ freeEdgeDensity d 2 (edgeIncl d n e) p :=
  ge_of_tendsto (dfi_free_density_eq_limit n e hp hp1)
    (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_nonneg (boxGraph d (n + k)) hp hp1 (by norm_num) _)


theorem ivd_freeEdgeDensity_le_one (n : ℕ) (e : Sym2 (boxVerts d n)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) : freeEdgeDensity d 2 (edgeIncl d n e) p ≤ 1 :=
  le_of_tendsto (dfi_free_density_eq_limit n e hp hp1)
    (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_le_one (boxGraph d (n + k)) hp hp1 (by norm_num) _)



theorem ivd_wiredEdgeDensity_le_one (n : ℕ) (e : Sym2 (boxVerts d n)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) : wiredEdgeDensity d 2 (edgeIncl d n e) p ≤ 1 :=
  le_of_tendsto (dfi_wired_density_eq_limit n e hp hp1)
    (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (n + k)) (boxBoundary d (n + k))
        hp hp1 (by norm_num) _)



noncomputable def ivd_freeAvgDensity (d n : ℕ) (p : ℝ) : ℝ :=
  (∑ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p)
    / ((boxGraph d n).edgeFinset.card : ℝ)



noncomputable def ivd_wiredAvgDensity (d n : ℕ) (p : ℝ) : ℝ :=
  (∑ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p)
    / ((boxGraph d n).edgeFinset.card : ℝ)


theorem ivd_freeAvgDensity_nonneg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ ivd_freeAvgDensity d n p := by
  unfold ivd_freeAvgDensity
  exact div_nonneg (Finset.sum_nonneg fun e _ => ivd_freeEdgeDensity_nonneg n e hp hp1)
    (by positivity)


theorem ivd_freeAvgDensity_le_one (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ivd_freeAvgDensity d n p ≤ 1 := by
  unfold ivd_freeAvgDensity
  rw [div_le_one hEpos]
  calc ∑ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p
      ≤ ∑ _e ∈ (boxGraph d n).edgeFinset, (1:ℝ) :=
        Finset.sum_le_sum fun e _ => ivd_freeEdgeDensity_le_one n e hp hp1
    _ = ((boxGraph d n).edgeFinset.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]


theorem ivd_wiredAvgDensity_le_one (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ivd_wiredAvgDensity d n p ≤ 1 := by
  unfold ivd_wiredAvgDensity
  rw [div_le_one hEpos]
  calc ∑ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p
      ≤ ∑ _e ∈ (boxGraph d n).edgeFinset, (1:ℝ) :=
        Finset.sum_le_sum fun e _ => ivd_wiredEdgeDensity_le_one n e hp hp1
    _ = ((boxGraph d n).edgeFinset.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]





theorem ivd_freeMeanOpenCount_le_avg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    fkMeanOpenCount (boxGraph d n) p 2
      ≤ ivd_freeAvgDensity d n p * ((boxGraph d n).edgeFinset.card : ℝ) := by
  unfold ivd_freeAvgDensity
  rw [div_mul_cancel₀ _ (ne_of_gt hEpos), fkMeanOpenCount_eq_sum_marginals]
  refine Finset.sum_le_sum fun e he => ?_
  rw [(edgeMargProb_fkProb (boxGraph d n) p 2 e).symm]
  have h1 := dfi_free_per_edge_le n n (le_refl n) e hp hp1
  rwa [ivd_innerEdgeLE_refl n e] at h1





theorem ivd_wiredMeanOpenCount_ge_avg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ivd_wiredAvgDensity d n p * ((boxGraph d n).edgeFinset.card : ℝ)
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (chOpenCount (boxGraph d n) ω : ℝ)
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  unfold ivd_wiredAvgDensity
  rw [div_mul_cancel₀ _ (ne_of_gt hEpos), ivd_wiredMeanOpenCount_eq_sum_marginals]
  refine Finset.sum_le_sum fun e he => ?_
  have h1 := dfi_wired_per_edge_ge n n (le_refl n) e hp hp1
  rwa [ivd_innerEdgeLE_refl n e] at h1











theorem den_openCount_upper_deviation_iv_avg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε ≤ 1 - ivd_freeAvgDensity d n p)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ε ≤ fkOpenCountLeProb (boxGraph d n) p 2
        ((ivd_freeAvgDensity d n p + ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
  set a := ivd_freeAvgDensity d n p with ha
  have ha0 : 0 ≤ a := ivd_freeAvgDensity_nonneg n hp hp1
  have hae1 : a + ε ≤ 1 := by linarith
  have hrm := reverse_markov_upper
      (fun ω : ConfigSpace (Sym2 (boxVerts d n)) => fkProb (boxGraph d n) p 2 ω)
      (fun ω => (chOpenCount (boxGraph d n) ω : ℝ))
      (fun ω => fkProb_nonneg (boxGraph d n) hp hp1 (by norm_num) ω)
      (fkProb_sum_eq_one (boxGraph d n) hp hp1 (by norm_num))
      (fun ω => by positivity)
      (M := ((boxGraph d n).edgeFinset.card : ℝ)) (μ := a) (ε := ε)
      (ivd_freeMeanOpenCount_le_avg n hp hp1 hEpos) ha0 hε hEpos
  have hε_le : ε ≤ ε / (a + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < a + ε)]; nlinarith
  exact le_trans hε_le hrm











theorem den_openCount_lower_deviation_iv_avg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ ivd_wiredAvgDensity d n p)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ε ≤ ivd_wiredOpenCountGeProb d n p
        ((ivd_wiredAvgDensity d n p - ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
  set b := ivd_wiredAvgDensity d n p with hb
  have hb1 : b ≤ 1 := ivd_wiredAvgDensity_le_one n hp hp1 hEpos
  have hrm := reverse_markov_lower
      (fun ω : ConfigSpace (Sym2 (boxVerts d n)) =>
        wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω)
      (fun ω => (chOpenCount (boxGraph d n) ω : ℝ))
      (M := ((boxGraph d n).edgeFinset.card : ℝ))
      (fun ω => wiredFkProb_nonneg (boxGraph d n) (boxBoundary d n) hp hp1 (by norm_num) ω)
      (wiredFkProb_sum_eq_one (boxGraph d n) (boxBoundary d n) hp hp1 (by norm_num))
      (fun ω => by
        change (chOpenCount (boxGraph d n) ω : ℝ) ≤ ((boxGraph d n).edgeFinset.card : ℝ)
        unfold chOpenCount; exact_mod_cast Finset.card_filter_le _ _)
      (ν := b) (ε := ε)
      (ivd_wiredMeanOpenCount_ge_avg n hp hp1 hEpos) hb1 hε hEpos
  have hε_le : ε ≤ ε / (1 - b + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - b + ε)]; nlinarith
  exact le_trans hε_le hrm

end FK

end StatMech

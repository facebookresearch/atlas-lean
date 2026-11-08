/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ThreeSeriesTailProb

public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Restatement of the main theorem: a.s. convergence of the partial sums
of an independent sequence forces summability of the tail probabilities. -/
example [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) {A : ℝ} (hA : A > 0)
    (hX_tend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => X i ω)) atTop (nhds (S ω))) :
    (∑' n, μ {ω | A < |X n ω|}) < ⊤ :=
  summable_tail_prob_of_ae_tendsto hX_meas hX_indep hA hX_tend

/-- Restatement of the contrapositive. -/
example [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X μ) {A : ℝ} (hA : A > 0)
    (hdiv : (∑' n, μ {ω | A < |X n ω|}) = ⊤) :
    ¬ ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => X i ω)) atTop (nhds (S ω)) :=
  not_ae_tendsto_partial_sum_of_tsum_tail_prob_eq_top hX_meas hX_indep hA hdiv

/-- The identically zero sequence is independent, its partial sums are
identically zero (hence converge a.s.), and its tail sets are empty, so
the tail-probability series is `0 < ⊤`. This pins the theorem on a
concrete case where every hypothesis is discharged from scratch. -/
example [IsProbabilityMeasure μ] {A : ℝ} (hA : A > 0) :
    (∑' n, μ {ω : Ω | A < |(fun _ : ℕ => fun _ : Ω => (0 : ℝ)) n ω|}) < ⊤ := by
  have hindep : iIndepFun (fun _ : ℕ => fun _ : Ω => (0 : ℝ)) μ := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets _
    by_cases h : ∀ i ∈ S, (0 : ℝ) ∈ sets i
    · have hpre : ∀ i ∈ S,
          (fun _ : ℕ => fun _ : Ω => (0 : ℝ)) i ⁻¹' sets i = Set.univ :=
        fun i hi => Set.preimage_const_of_mem (h i hi)
      have hbi :
          (⋂ j ∈ S,
            (fun _ : ℕ => fun _ : Ω => (0 : ℝ)) j ⁻¹' sets j) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro ω
        refine Set.mem_iInter₂.mpr ?_
        intro j hj
        rw [hpre j hj]
        exact Set.mem_univ ω
      rw [hbi, measure_univ]
      exact (Finset.prod_eq_one
        (fun i hi => by rw [hpre i hi, measure_univ])).symm
    · push Not at h
      obtain ⟨i, hi, hi0⟩ := h
      have hpre : (fun _ : ℕ => fun _ : Ω => (0 : ℝ)) i ⁻¹' sets i = ∅ :=
        Set.preimage_const_of_notMem hi0
      have hbi :
          (⋂ j ∈ S,
            (fun _ : ℕ => fun _ : Ω => (0 : ℝ)) j ⁻¹' sets j) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        have hωi := (Set.mem_iInter₂.mp hω) i hi
        rw [hpre] at hωi
        exact hωi
      rw [hbi, measure_empty]
      exact (Finset.prod_eq_zero hi (by rw [hpre, measure_empty])).symm
  have hX_tend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i =>
        (fun _ : ℕ => fun _ : Ω => (0 : ℝ)) i ω)) atTop (nhds (S ω)) :=
    ⟨fun _ => 0, Filter.Eventually.of_forall fun _ => by
      simp⟩
  exact summable_tail_prob_of_ae_tendsto (fun _ => measurable_const)
    hindep hA hX_tend

end ProbabilityTheory

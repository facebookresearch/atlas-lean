/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovThreeSeries

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.KolmogorovThreeSeries

/-- The identically zero sequence of random variables. -/
def zeroSeq (Ω : Type*) : ℕ → Ω → ℝ := fun _ _ => 0

/-- The constant zero sequence is independently distributed: every
coordinate generates the trivial `σ`-algebra. -/
theorem iIndepFun_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    iIndepFun (zeroSeq Ω) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases hall : ∀ i ∈ S, (0 : ℝ) ∈ sets i
  · have hpre : ∀ i ∈ S, (zeroSeq Ω i) ⁻¹' sets i = Set.univ := by
      intro i hi
      ext ω
      simp only [Set.mem_preimage, zeroSeq, Set.mem_univ, iff_true]
      exact hall i hi
    have hInter : (⋂ i ∈ S, (zeroSeq Ω i) ⁻¹' sets i) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      rw [Set.mem_iInter₂]
      intro i hi
      rw [hpre i hi]
      trivial
    rw [hInter, measure_univ]
    symm
    apply Finset.prod_eq_one
    intro i hi
    rw [hpre i hi, measure_univ]
  · push Not at hall
    obtain ⟨i, hi, hni⟩ := hall
    have hpre : (zeroSeq Ω i) ⁻¹' sets i = ∅ := by
      ext ω
      simp only [Set.mem_preimage, zeroSeq, Set.mem_empty_iff_false, iff_false]
      exact hni
    have hInter : (⋂ j ∈ S, (zeroSeq Ω j) ⁻¹' sets j) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have := Set.mem_iInter₂.mp hω i hi
      rw [hpre] at this
      exact this
    rw [hInter, measure_empty]
    symm
    apply Finset.prod_eq_zero hi
    show μ ((zeroSeq Ω) i ⁻¹' sets i) = 0
    rw [hpre, measure_empty]

/-- The truncation of the zero sequence is the zero sequence. -/
theorem truncatedRV_zero {Ω : Type*} [MeasurableSpace Ω] (A : ℝ) (n : ℕ) :
    ProbabilityTheory.KolmogorovThreeSeries.truncatedRV
      (zeroSeq Ω) A n = fun _ => (0 : ℝ) := by
  ext ω
  show (zeroSeq Ω) n ω * Set.indicator {ω | |(zeroSeq Ω) n ω| ≤ A} 1 ω = 0
  simp [zeroSeq]

/-- The general API restates with the exact public signature. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun (m := fun _ => inferInstance) X μ)
    (A : ℝ) (hA : A > 0)
    (h1 : (∑' n, μ {ω | |X n ω| > A}) < ⊤)
    (h2 : Summable fun n => ∫ ω, (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω ∂μ)
    (h3 : Summable fun n =>
      variance (fun ω => (X n ω) * Set.indicator {ω | |X n ω| ≤ A} 1 ω) μ) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Filter.Tendsto (fun n =>
      (Finset.range n).sum (fun i => X i ω))
      Filter.atTop (nhds (S ω)) :=
  ProbabilityTheory.KolmogorovThreeSeries.kolmogorov_three_series_sufficiency
    hX_meas hX_indep A hA h1 h2 h3

/-- The centered-convergence lemma restates with the exact public signature. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → ℝ}
    (hZ_sm : ∀ n, StronglyMeasurable (Z n))
    (hZ_indep : iIndepFun (m := fun _ => inferInstance) Z μ)
    (hZ_mean : ∀ n, ∫ ω, Z n ω ∂μ = 0)
    (hZ_int : ∀ n, Integrable (Z n) μ)
    {R : NNReal}
    (hZ_L1_bdd : ∀ n, eLpNorm (fun ω => ∑ k ∈ range (n + 1), Z k ω) 1 μ ≤ ↑R) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => ∑ k ∈ range (n + 1), Z k ω) atTop (nhds c) :=
  ProbabilityTheory.ae_tendsto_sum_of_indep_centered_L1bdd hZ_sm hZ_indep
    hZ_mean hZ_int hZ_L1_bdd

/-- Zero sequence: all three series are zero, so the (zero) partial sums
converge almost surely. This is the concrete instance of the sufficiency
theorem. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Filter.Tendsto (fun n =>
      (Finset.range n).sum (fun i => (zeroSeq Ω) i ω))
      Filter.atTop (nhds (S ω)) := by
  apply ProbabilityTheory.KolmogorovThreeSeries.kolmogorov_three_series_sufficiency
    (X := zeroSeq Ω)
    (fun _ => measurable_const) iIndepFun_zero 1 one_pos
  · have hterm : ∀ n : ℕ, μ {ω : Ω | |(zeroSeq Ω) n ω| > (1 : ℝ)} = 0 := by
      intro n
      have hset : {ω : Ω | |(zeroSeq Ω) n ω| > (1 : ℝ)} = ∅ := by
        ext ω
        simp [zeroSeq]
      rw [hset, measure_empty]
    simp [hterm]
  · have hfun : (fun n : ℕ => ∫ ω, (zeroSeq Ω) n ω *
        Set.indicator {ω | |(zeroSeq Ω) n ω| ≤ (1 : ℝ)} 1 ω ∂μ) = fun _ => (0 : ℝ) := by
      funext n
      simp [zeroSeq]
    rw [hfun]
    exact summable_zero
  · have hfun : (fun n : ℕ => variance (fun ω => (zeroSeq Ω) n ω *
        Set.indicator {ω | |(zeroSeq Ω) n ω| ≤ (1 : ℝ)} 1 ω) μ) = fun _ => (0 : ℝ) := by
      funext n
      have hzero : (fun ω => (zeroSeq Ω) n ω *
          Set.indicator {ω | |(zeroSeq Ω) n ω| ≤ (1 : ℝ)} 1 ω) = fun _ => (0 : ℝ) := by
        funext ω
        simp [zeroSeq]
      rw [hzero]
      exact variance_zero μ
    rw [hfun]
    exact summable_zero

/-- Zero centered sequence: the partial sums are identically zero, hence
converge almost surely. Concrete instance of the centered-convergence lemma. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto
      (fun n => ∑ k ∈ range (n + 1), (zeroSeq Ω) k ω)
      atTop (nhds c) := by
  apply ProbabilityTheory.ae_tendsto_sum_of_indep_centered_L1bdd
    (Z := zeroSeq Ω) (R := 0)
    (fun _ => stronglyMeasurable_const) iIndepFun_zero
  · intro n
    simp [zeroSeq]
  · intro n
    exact integrable_const _
  · intro n
    have hsum : (fun ω => ∑ k ∈ range (n + 1), (zeroSeq Ω) k ω) = fun _ => (0 : ℝ) := by
      funext ω
      simp [zeroSeq]
    rw [hsum]
    simp

-- `#print axioms` for the public declarations: only the standard triple.
#print axioms ProbabilityTheory.ae_tendsto_sum_of_indep_centered_L1bdd
#print axioms ProbabilityTheory.KolmogorovThreeSeries.truncatedRV
#print axioms ProbabilityTheory.KolmogorovThreeSeries.ae_tendsto_centered_of_indep_summableVar
#print axioms ProbabilityTheory.KolmogorovThreeSeries.ae_eventually_truncation_eq
#print axioms ProbabilityTheory.KolmogorovThreeSeries.ae_tendsto_of_ae_eventually_eq_and_ae_tendsto
#print axioms ProbabilityTheory.KolmogorovThreeSeries.ae_tendsto_truncated_of_conditions
#print axioms ProbabilityTheory.KolmogorovThreeSeries.kolmogorov_three_series_sufficiency
#print axioms MathlibExtTest.Probability.KolmogorovThreeSeries.iIndepFun_zero

end MathlibExtTest.Probability.KolmogorovThreeSeries

end

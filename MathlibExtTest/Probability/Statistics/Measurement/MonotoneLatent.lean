/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.MonotoneLatent

/-!
# Tests for monotone latent curves

Two latent states under the uniform law and two items: the chain
curves (1/4, 3/4) give observed covariance 1/16, while the opposite
curves give -1/16, so monotonicity cannot be dropped.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory

/-! # Tests: nonvacuity obligations

Two latent states `Fin 2` under the uniform law, two items `Fin 2`, item `0` vs item `1`.
Chain: both curves `(1/4, 3/4)` (monotone), observed covariance `1/16`.
Opposite curves: item `0` is `(1/4, 3/4)`, item `1` is `(3/4, 1/4)` (antitone, not monotone),
observed covariance `-1/16`; the monotonicity hypothesis cannot be dropped. -/

/-- The uniform law on two latent states. -/
private noncomputable def halfPMF : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => 2⁻¹) (by rw [Fin.sum_univ_two, ENNReal.inv_two_add_inv_two])

private noncomputable def chainCurve : Fin 2 → Fin 2 → ℝ := fun z _ => ![1 / 4, 3 / 4] z

private noncomputable def oppCurve : Fin 2 → Fin 2 → ℝ := ![![1 / 4, 3 / 4], ![3 / 4, 1 / 4]]

private theorem chainCurve_nonneg : ∀ z i, 0 ≤ chainCurve z i := by
  intro z i; fin_cases z <;> norm_num [chainCurve]

private theorem chainCurve_le_one : ∀ z i, chainCurve z i ≤ 1 := by
  intro z i; fin_cases z <;> norm_num [chainCurve]

private theorem oppCurve_nonneg : ∀ z i, 0 ≤ oppCurve z i := by
  intro z i; fin_cases z <;> fin_cases i <;> norm_num [oppCurve]

private theorem oppCurve_le_one : ∀ z i, oppCurve z i ≤ 1 := by
  intro z i; fin_cases z <;> fin_cases i <;> norm_num [oppCurve]

private theorem test_chain_hypotheses :
    (Monotone fun z => chainCurve z 0) ∧ (Monotone fun z => chainCurve z 1) := by
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact le_rfl
    · norm_num [chainCurve]
    · exact absurd hab (by decide)
    · exact le_rfl
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact le_rfl
    · norm_num [chainCurve]
    · exact absurd hab (by decide)
    · exact le_rfl

private theorem test_chain_covariance :
    ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
      (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
      (halfPMF.bind fun z =>
        localIndepPMF (chainCurve z) (chainCurve_nonneg z) (chainCurve_le_one z)).toMeasure
      = 1 / 16 := by
  have hMix := latentMixture_coordinate_moments halfPMF chainCurve chainCurve_nonneg
    chainCurve_le_one
  obtain ⟨h1, h2, h3⟩ := hMix
  have hEq := h3 0 1 (by decide)
  rw [hEq]
  simp only [MathlibExt.Probability.FiniteProbability.covariance,
    MathlibExt.Probability.FiniteProbability.expectation, Fin.sum_univ_two]
  have hpmf0 : (halfPMF 0).toReal = 1 / 2 := by simp [halfPMF]
  have hpmf1 : (halfPMF 1).toReal = 1 / 2 := by simp [halfPMF]
  have hc00 : chainCurve 0 0 = 1 / 4 := by norm_num [chainCurve]
  have hc01 : chainCurve 0 1 = 1 / 4 := by norm_num [chainCurve]
  have hc10 : chainCurve 1 0 = 3 / 4 := by norm_num [chainCurve]
  have hc11 : chainCurve 1 1 = 3 / 4 := by norm_num [chainCurve]
  rw [hpmf0, hpmf1, hc00, hc01, hc10, hc11]
  norm_num

private theorem test_chain_covariance_nonneg :
    0 ≤ ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
      (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
      (halfPMF.bind fun z =>
        localIndepPMF (chainCurve z) (chainCurve_nonneg z) (chainCurve_le_one z)).toMeasure :=
  covariance_items_nonneg_of_monotone halfPMF chainCurve chainCurve_nonneg chainCurve_le_one
    (by decide) test_chain_hypotheses.1 test_chain_hypotheses.2

private theorem test_opposite_hypotheses :
    (Monotone fun z => oppCurve z 0) ∧ (Antitone fun z => oppCurve z 1) ∧
      ¬ Monotone fun z => oppCurve z 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact le_rfl
    · norm_num [oppCurve]
    · exact absurd hab (by decide)
    · exact le_rfl
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact le_rfl
    · norm_num [oppCurve]
    · exact absurd hab (by decide)
    · exact le_rfl
  · intro h
    have h' := h (show (0 : Fin 2) ≤ 1 by decide)
    norm_num [oppCurve] at h'

private theorem test_opposite_covariance :
    ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
      (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
      (halfPMF.bind fun z =>
        localIndepPMF (oppCurve z) (oppCurve_nonneg z) (oppCurve_le_one z)).toMeasure
      = -1 / 16 := by
  have hMix := latentMixture_coordinate_moments halfPMF oppCurve oppCurve_nonneg oppCurve_le_one
  obtain ⟨h1, h2, h3⟩ := hMix
  have hEq := h3 0 1 (by decide)
  rw [hEq]
  simp only [MathlibExt.Probability.FiniteProbability.covariance,
    MathlibExt.Probability.FiniteProbability.expectation, Fin.sum_univ_two]
  have hpmf0 : (halfPMF 0).toReal = 1 / 2 := by simp [halfPMF]
  have hpmf1 : (halfPMF 1).toReal = 1 / 2 := by simp [halfPMF]
  have ho00 : oppCurve 0 0 = 1 / 4 := by norm_num [oppCurve]
  have ho10 : oppCurve 1 0 = 3 / 4 := by norm_num [oppCurve]
  have ho01 : oppCurve 0 1 = 3 / 4 := by norm_num [oppCurve]
  have ho11 : oppCurve 1 1 = 1 / 4 := by norm_num [oppCurve]
  rw [hpmf0, hpmf1, ho00, ho10, ho01, ho11]
  norm_num


end MathlibExt.Probability.Statistics.Measurement

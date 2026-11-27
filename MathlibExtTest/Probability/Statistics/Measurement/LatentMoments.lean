/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.LatentMoments

/-!
# Latent-mixture moment tests

Two-state rational, boundary, and degenerate-prior instances.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement

theorem pi_norm_rational :
    (∑ z : Fin 2, (if z = 0 then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))) = 1 := by
  rw [Fin.sum_univ_two]
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h1, ite_true, ite_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem hq0_rational_all : ∀ z i : Fin 2, 0 ≤ (if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
    else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ))) := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num

theorem hq1_rational_all : ∀ z i : Fin 2, (if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
    else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ))) ≤ 1 := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num

theorem pi_norm_boundary :
    (∑ z : Fin 2, (if z = 0 then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))) = 1 := by
  rw [Fin.sum_univ_two]
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h1, ite_true, ite_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem hq0_boundary_all : ∀ z i : Fin 2, 0 ≤ (if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
    else (if i = 0 then (1 : ℝ) else (0 : ℝ))) := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi]
  · by_cases hi : i = 0 <;> simp [hz, hi]

theorem hq1_boundary_all : ∀ z i : Fin 2, (if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
    else (if i = 0 then (1 : ℝ) else (0 : ℝ))) ≤ 1 := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi]
  · by_cases hi : i = 0 <;> simp [hz, hi]

theorem pi_norm_degenerate :
    (∑ z : Fin 2, (if z = 0 then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))) = 1 := by
  rw [Fin.sum_univ_two]
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h1, ite_true, ite_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem hq0_degenerate_all : ∀ z i : Fin 2, 0 ≤ (if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
    else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ))) := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num

theorem hq1_degenerate_all : ∀ z i : Fin 2, (if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
    else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ))) ≤ 1 := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num

/-! ## Production result (the leaf's one new public symbol) -/

theorem latentMixture_fin2_rational_moments :
    (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
            (by exact pi_norm_rational)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
              else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
            (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = 7 / 12)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
            (by exact pi_norm_rational)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
              else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
            (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = 17 / 120)
    ∧ (ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
        (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
        ((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
            (by exact pi_norm_rational)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
              else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
            (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = -1 / 30)
    ∧ (∑ x, (((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
            (by exact pi_norm_rational)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
              else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
            (by exact hq0_rational_all z) (by exact hq1_rational_all z))) x).toReal = 1) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hMom := MathlibExt.Probability.Statistics.Measurement.latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
        then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ)) pi_norm_rational)
    (fun z i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
      else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
    hq0_rational_all hq1_rational_all
  have c1 : (∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
          (by exact pi_norm_rational)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
            else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
          (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = 7 / 12) := by
    have h1 := hMom.1 (0 : Fin 2)
    convert h1 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/3)]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2/3)]
    norm_num
  have c2 : (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
          (by exact pi_norm_rational)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
            else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
          (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = 17 / 120) := by
    have h2 := hMom.2.1 (0 : Fin 2) (1 : Fin 2) h01
    convert h2 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/3)]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2/3)]
    norm_num
  have c3 : (ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
      (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
      ((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
          (by exact pi_norm_rational)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
            else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
          (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = -1 / 30) := by
    have h3 := hMom.2.2 (0 : Fin 2) (1 : Fin 2) h01
    convert h3 using 2
    rw [MathlibExt.Probability.FiniteProbability.covariance_eq_sub (MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one _)]
    unfold MathlibExt.Probability.FiniteProbability.expectation
    simp only [Fin.sum_univ_two, PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/3)]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2/3)]
    norm_num
  have c4 : (∑ x, (((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
          (by exact pi_norm_rational)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
            else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
          (by exact hq0_rational_all z) (by exact hq1_rational_all z))) x).toReal = 1) :=
    MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one _
  exact ⟨c1, c2, c3, c4⟩

/-- Boundary cells: curves attain `0` and `1`. `Z = Fin 2` with equal
weights `1/2, 1/2`; curves `z=0: (0, 1)`, `z=1: (1, 0)`. Then
`E[Y_0] = 1/2`, `E[Y_0 * Y_1] = 0`, `Cov(Y_0, Y_1) = -1/4`. This pins that
closed `[0, 1]` endpoints need no strict-positivity side condition. -/
theorem latentMixture_boundary_moments :
    (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
            (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
              else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
            (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = 1 / 2)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
            (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
              else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
            (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = 0)
    ∧ (ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
        (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
        ((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
            (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
              else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
            (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = -1 / 4) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hMom := MathlibExt.Probability.Statistics.Measurement.latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
        then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ)) pi_norm_boundary)
    (fun z i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
      else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
    hq0_boundary_all hq1_boundary_all
  have c1 : (∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
          (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
            else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
          (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = 1 / 2) := by
    have h1 := hMom.1 (0 : Fin 2)
    convert h1 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  have c2 : (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
          (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
            else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
          (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = 0) := by
    have h2 := hMom.2.1 (0 : Fin 2) (1 : Fin 2) h01
    convert h2 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  have c3 : (ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
      (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
      ((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
          (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
            else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
          (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = -1 / 4) := by
    have h3 := hMom.2.2 (0 : Fin 2) (1 : Fin 2) h01
    convert h3 using 2
    rw [MathlibExt.Probability.FiniteProbability.covariance_eq_sub (MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one _)]
    unfold MathlibExt.Probability.FiniteProbability.expectation
    simp only [Fin.sum_univ_two, PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  exact ⟨c1, c2, c3⟩

/-- Degenerate prior: weights `(1, 0)` put all mass on latent state `0`, so
the mixture collapses to that component. Curves `z=0: (2/7, 5/9)`,
`z=1: (1/3, 1/3)` (the zero-weight state's curves are irrelevant). Then
`E[Y_0] = 2/7` and `E[Y_0 * Y_1] = (2/7) * (5/9)`. This pins that `pi z = 0`
cells are allowed. -/
theorem latentMixture_degenerate_prior_moments :
    (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))
            (by exact pi_norm_degenerate)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
              else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
            (by exact hq0_degenerate_all z) (by exact hq1_degenerate_all z))).toMeasure = 2 / 7)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))
            (by exact pi_norm_degenerate)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
              else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
            (by exact hq0_degenerate_all z) (by exact hq1_degenerate_all z))).toMeasure = (2 / 7 : ℝ) * (5 / 9)) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hMom := MathlibExt.Probability.Statistics.Measurement.latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
        then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ)) pi_norm_degenerate)
    (fun z i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
      else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
    hq0_degenerate_all hq1_degenerate_all
  have c1 : (∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))
          (by exact pi_norm_degenerate)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
            else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
          (by exact hq0_degenerate_all z) (by exact hq1_degenerate_all z))).toMeasure = 2 / 7) := by
    have h1 := hMom.1 (0 : Fin 2)
    convert h1 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (1:ℝ))]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (0:ℝ))]
    norm_num
  have c2 : (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))
          (by exact pi_norm_degenerate)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
            else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
          (by exact hq0_degenerate_all z) (by exact hq1_degenerate_all z))).toMeasure
        = (2 / 7 : ℝ) * (5 / 9)) := by
    have h2 := hMom.2.1 (0 : Fin 2) (1 : Fin 2) h01
    convert h2 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (1:ℝ))]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (0:ℝ))]
    norm_num
  exact ⟨c1, c2⟩


end MathlibExtTest.Probability.Statistics.Measurement

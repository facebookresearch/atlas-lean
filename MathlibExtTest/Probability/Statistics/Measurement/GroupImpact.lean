/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.GroupImpact
public import MathlibExt.Probability.Statistics.Measurement.FactorAnalysis

/-!
# Tests for group impact under equal item curves

On two latent states and one item: equal curves with different latent
laws give a nonzero marginal difference (impact without differential
item functioning), different curves can give equal marginals, and the
unanchored-scale examples show why a common scale is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix

namespace MathlibExtTest.Probability.Statistics.Measurement

open MathlibExt.Probability.Statistics.Measurement

/-! Fixtures. Latent state `0` is low, `1` is high; one item, `Fin 1`. -/

private theorem norm_low_heavy :
    (∑ z : Fin 2, (if z = 0 then ENNReal.ofReal (3 / 4 : ℝ)
      else ENNReal.ofReal (1 / 4 : ℝ))) = 1 := by
  rw [Fin.sum_univ_two]
  simp only [ite_true, one_ne_zero, ite_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

private theorem norm_high_heavy :
    (∑ z : Fin 2, (if z = 0 then ENNReal.ofReal (1 / 4 : ℝ)
      else ENNReal.ofReal (3 / 4 : ℝ))) = 1 := by
  rw [Fin.sum_univ_two]
  simp only [ite_true, one_ne_zero, ite_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

private theorem norm_equal :
    (∑ z : Fin 2, (if z = 0 then ENNReal.ofReal (1 / 2 : ℝ)
      else ENNReal.ofReal (1 / 2 : ℝ))) = 1 := by
  rw [Fin.sum_univ_two]
  simp only [ite_true, one_ne_zero, ite_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Increasing curve `(1/4, 3/4)` over the two latent states. -/
private theorem rising_0 : ∀ (z : Fin 2) (_ : Fin 1),
    0 ≤ (if z = 0 then (1 / 4 : ℝ) else 3 / 4) := by
  intro z _; split_ifs <;> norm_num

private theorem rising_1 : ∀ (z : Fin 2) (_ : Fin 1),
    (if z = 0 then (1 / 4 : ℝ) else 3 / 4) ≤ 1 := by
  intro z _; split_ifs <;> norm_num

/-- Flat curve `(1/2, 1/2)`. -/
private theorem flat_0 : ∀ (_ : Fin 2) (_ : Fin 1), 0 ≤ (1 / 2 : ℝ) := by
  intro _ _; norm_num

private theorem flat_1 : ∀ (_ : Fin 2) (_ : Fin 1), (1 / 2 : ℝ) ≤ 1 := by
  intro _ _; norm_num

/-- Impact without DIF: both groups share the curve `(1/4, 3/4)`; latent laws
`(3/4, 1/4)` and `(1/4, 3/4)` give marginals `3/8` and `5/8`, and the impact
identity evaluates to `-1/4`. -/
private theorem impact_without_dif :
    (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (3 / 4 : ℝ) else ENNReal.ofReal (1 / 4 : ℝ))
            norm_low_heavy).bind (fun z => localIndepPMF
            (fun _ : Fin 1 => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
            (rising_0 z) (rising_1 z))).toMeasure = 3 / 8)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 4 : ℝ) else ENNReal.ofReal (3 / 4 : ℝ))
            norm_high_heavy).bind (fun z => localIndepPMF
            (fun _ : Fin 1 => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
            (rising_0 z) (rising_1 z))).toMeasure = 5 / 8)
    ∧ (∑ z : Fin 2,
        (((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (3 / 4 : ℝ) else ENNReal.ofReal (1 / 4 : ℝ))
            norm_low_heavy) z).toReal
          - ((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 4 : ℝ) else ENNReal.ofReal (3 / 4 : ℝ))
            norm_high_heavy) z).toReal)
        * (if z = 0 then (1 / 4 : ℝ) else 3 / 4) = -1 / 4) := by
  have hA := (latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
      then ENNReal.ofReal (3 / 4 : ℝ) else ENNReal.ofReal (1 / 4 : ℝ)) norm_low_heavy)
    (fun z (_ : Fin 1) => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
    rising_0 rising_1).1 0
  simp only [MathlibExt.Probability.FiniteProbability.expectation, Fin.sum_univ_two,
    PMF.ofFintype_apply, ite_true, one_ne_zero, ite_false,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 3 / 4 by norm_num),
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 4 by norm_num)] at hA
  have hB := (latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
      then ENNReal.ofReal (1 / 4 : ℝ) else ENNReal.ofReal (3 / 4 : ℝ)) norm_high_heavy)
    (fun z (_ : Fin 1) => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
    rising_0 rising_1).1 0
  simp only [MathlibExt.Probability.FiniteProbability.expectation, Fin.sum_univ_two,
    PMF.ofFintype_apply, ite_true, one_ne_zero, ite_false,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 3 / 4 by norm_num),
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 4 by norm_num)] at hB
  refine ⟨by rw [hA]; norm_num, by rw [hB]; norm_num, ?_⟩
  simp only [Fin.sum_univ_two, PMF.ofFintype_apply, ite_true, one_ne_zero, ite_false,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 3 / 4 by norm_num),
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 4 by norm_num)]
  norm_num

/-- Impact without DIF, through the pinned identity: applying
`impact_difference_of_equal_curves` to the shared-curve fixture above gives
impact `-1/4`; with group B's marginal `5/8`, the same application yields
group A's marginal `3/8`. -/
private theorem impact_without_dif_by_identity :
    (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (3 / 4 : ℝ) else ENNReal.ofReal (1 / 4 : ℝ))
            norm_low_heavy).bind (fun z => localIndepPMF
            (fun _ : Fin 1 => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
            (rising_0 z) (rising_1 z))).toMeasure
      - ∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 4 : ℝ) else ENNReal.ofReal (3 / 4 : ℝ))
            norm_high_heavy).bind (fun z => localIndepPMF
            (fun _ : Fin 1 => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
            (rising_0 z) (rising_1 z))).toMeasure = -1 / 4)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (3 / 4 : ℝ) else ENNReal.ofReal (1 / 4 : ℝ))
            norm_low_heavy).bind (fun z => localIndepPMF
            (fun _ : Fin 1 => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
            (rising_0 z) (rising_1 z))).toMeasure = 3 / 8)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 4 : ℝ) else ENNReal.ofReal (3 / 4 : ℝ))
            norm_high_heavy).bind (fun z => localIndepPMF
            (fun _ : Fin 1 => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
            (rising_0 z) (rising_1 z))).toMeasure = 5 / 8) := by
  have himpact := impact_difference_of_equal_curves
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
      then ENNReal.ofReal (3 / 4 : ℝ) else ENNReal.ofReal (1 / 4 : ℝ)) norm_low_heavy)
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
      then ENNReal.ofReal (1 / 4 : ℝ) else ENNReal.ofReal (3 / 4 : ℝ)) norm_high_heavy)
    (fun z (_ : Fin 1) => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
    (fun z (_ : Fin 1) => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
    rising_0 rising_1 rising_0 rising_1 0 (fun _ => rfl)
  simp only [Fin.sum_univ_two, PMF.ofFintype_apply, ite_true, one_ne_zero, ite_false,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 3 / 4 by norm_num),
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 4 by norm_num)] at himpact
  have hB := (latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
      then ENNReal.ofReal (1 / 4 : ℝ) else ENNReal.ofReal (3 / 4 : ℝ)) norm_high_heavy)
    (fun z (_ : Fin 1) => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
    rising_0 rising_1).1 0
  simp only [MathlibExt.Probability.FiniteProbability.expectation, Fin.sum_univ_two,
    PMF.ofFintype_apply, ite_true, one_ne_zero, ite_false,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 3 / 4 by norm_num),
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 4 by norm_num)] at hB
  refine ⟨by rw [himpact]; norm_num, ?_, by rw [hB]; norm_num⟩
  linarith

/-- DIF without impact: under the equal latent law `(1/2, 1/2)`, the differing
curves `(1/4, 3/4)` and `(1/2, 1/2)` both give marginal `1/2`. -/
private theorem dif_without_impact :
    (∃ z : Fin 2, (if z = 0 then (1 / 4 : ℝ) else 3 / 4) ≠ 1 / 2)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
            norm_equal).bind (fun z => localIndepPMF
            (fun _ : Fin 1 => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
            (rising_0 z) (rising_1 z))).toMeasure = 1 / 2)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
            norm_equal).bind (fun z => localIndepPMF
            (fun _ : Fin 1 => (1 / 2 : ℝ))
            (flat_0 z) (flat_1 z))).toMeasure = 1 / 2) := by
  have hex : (if (0 : Fin 2) = 0 then (1 / 4 : ℝ) else 3 / 4) ≠ 1 / 2 := by
    rw [ite_eq_left rfl]
    norm_num
  have hR := (latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
      then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ)) norm_equal)
    (fun z (_ : Fin 1) => if z = 0 then (1 / 4 : ℝ) else 3 / 4)
    rising_0 rising_1).1 0
  simp only [MathlibExt.Probability.FiniteProbability.expectation, Fin.sum_univ_two,
    PMF.ofFintype_apply, ite_true, one_ne_zero, ite_false,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num)] at hR
  have hF := (latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
      then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ)) norm_equal)
    (fun _ : Fin 2 => fun _ : Fin 1 => (1 / 2 : ℝ))
    flat_0 flat_1).1 0
  simp only [MathlibExt.Probability.FiniteProbability.expectation, Fin.sum_univ_two,
    PMF.ofFintype_apply, ite_true, one_ne_zero, ite_false,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num)] at hF
  exact ⟨⟨0, hex⟩, by rw [hR]; norm_num, by rw [hF]; norm_num⟩

/-- Unanchored scales, item-response form (existing `twoPLPMF_affine_of_pos`):
a group-specific rescale `θ ↦ 2θ + 1` makes the same observed law sit at
latent locations `0` and `1`; fixing one anchor item forces the identity map
(existing `affine_eq_of_anchor`). -/
private theorem unanchored_twoPL_rescale :
    twoPLPMF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0) 0
      = twoPLPMF (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => 1) 1
    ∧ (0 : ℝ) ≠ 1
    ∧ ∀ A B : ℝ, A ≠ 0 → (1 : ℝ) / A = 1 → A * 0 + B = 0 → A = 1 ∧ B = 0 := by
  have h := (twoPLPMF_affine_of_pos (fun _ : Fin 1 => (1 : ℝ)) (fun _ => (0 : ℝ))
    (0 : ℝ) 2 1 (by norm_num) (fun _ => by norm_num)).2
  have hb : (fun _ : Fin 1 => (2 : ℝ) * 0 + 1) = (fun _ : Fin 1 => (1 : ℝ)) := by
    funext i
    norm_num
  have hth : (2 : ℝ) * (0 : ℝ) + 1 = 1 := by norm_num
  have heq : twoPLPMF (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0) 0
      = twoPLPMF (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ => 1) 1 := by
    simpa [hb, hth] using h
  refine ⟨heq, by norm_num, ?_⟩
  intro A B hA hda hdb
  exact affine_eq_of_anchor (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))
    0 A B hA (by norm_num) hda hdb

/-- Unanchored scales, two-group factor form (existing
`twoGroup_affine_indeterminacy`) at one indicator and one factor. -/
private theorem unanchored_twoGroup_factor :
    ∃ (U : Fin 2 → Matrix (Fin 1) (Fin 1) ℝ) (β : Fin 2 → (Fin 1 → ℝ)),
      (∀ g, IsUnit (U g).det) ∧
      (∀ g, ProbabilityTheory.multivariateGaussian
          ((WithLp.equiv 2 _).symm (factorModelMean 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) 0))
          (factorModelCov (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1)
        = ProbabilityTheory.multivariateGaussian
          ((WithLp.equiv 2 _).symm
            (factorModelMean (0 + (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ β g)
              ((1 : Matrix (Fin 1) (Fin 1) ℝ) * U g) ((U g)⁻¹ *ᵥ (0 - β g))))
          (factorModelCov ((1 : Matrix (Fin 1) (Fin 1) ℝ) * U g)
            ((U g)⁻¹ * 1 * (U g)⁻¹ᵀ) 1)) ∧
      (U 0)⁻¹ *ᵥ (0 - β 0) ≠ (U 1)⁻¹ *ᵥ (0 - β 1) := by
  exact twoGroup_affine_indeterminacy (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 1 1

end MathlibExtTest.Probability.Statistics.Measurement

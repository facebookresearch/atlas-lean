/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.IsotropicConstant
public import MathlibExt.Probability.Geometry.LogConcaveUniform
public import Mathlib.Tactic.FieldSimp

/-!
# Normalized convex-body laws and their entropy

Source: `constants/20b.md` and Klartag--Lehec, arXiv:2412.15044v1,
Introduction: λ_K is actual normalized volume and Ent(λ_K)=log Vol(K).
-/

@[expose] public section

namespace MathlibExt.Probability.IsotropicConstant

open MeasureTheory
open scoped ENNReal

theorem bodyVolume_pos {n : ℕ} (K : FullDimensionalBody n) :
    0 < volume (K.body : Set (EuclideanSpace ℝ (Fin n))) :=
  Measure.measure_pos_of_nonempty_interior volume K.interior_nonempty

theorem bodyVolume_ne_top {n : ℕ} (K : FullDimensionalBody n) :
    volume (K.body : Set (EuclideanSpace ℝ (Fin n))) ≠ ⊤ :=
  K.body.isCompact.measure_ne_top

/-- The actual normalized indicator density of a convex body. -/
noncomputable def bodyDensity {n : ℕ} (K : FullDimensionalBody n) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  (K.body : Set (EuclideanSpace ℝ (Fin n))).indicator
    (fun _ => (volume (K.body : Set (EuclideanSpace ℝ (Fin n))))⁻¹.toReal)

theorem bodyDensity_logConcave {n : ℕ} (K : FullDimensionalBody n) :
    ThinShell.IsLogConcaveDensity (bodyDensity K) := by
  apply ThinShell.isLogConcaveDensity_indicator_const K.body.convex K.body.isCompact.measurableSet
  exact ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr (bodyVolume_ne_top K))
    (ENNReal.inv_ne_top.mpr (bodyVolume_pos K).ne')

theorem bodyLaw_probability {n : ℕ} (K : FullDimensionalBody n) :
    IsProbabilityMeasure (bodyLaw K) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite (bodyVolume_pos K).ne'
    (bodyVolume_ne_top K)

theorem bodyLaw_eq_withDensity {n : ℕ} (K : FullDimensionalBody n) :
    bodyLaw K = volume.withDensity (fun x => ENNReal.ofReal (bodyDensity K x)) :=
  ThinShell.cond_eq_withDensity_indicator volume K.body.isCompact.measurableSet
    (bodyVolume_pos K).ne'

theorem bodyLaw_integrable_coord {n : ℕ} (K : FullDimensionalBody n) (i : Fin n) :
    Integrable (fun x => x i) (bodyLaw K) := by
  apply (integrable_smul_measure (ENNReal.inv_ne_zero.mpr (bodyVolume_ne_top K))
    (ENNReal.inv_ne_top.mpr (bodyVolume_pos K).ne')).mpr
  exact ContinuousOn.integrableOn_compact K.body.isCompact
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousOn

theorem bodyLaw_integrable_coord_mul {n : ℕ} (K : FullDimensionalBody n) (i j : Fin n) :
    Integrable (fun x => x i * x j) (bodyLaw K) := by
  apply (integrable_smul_measure (ENNReal.inv_ne_zero.mpr (bodyVolume_ne_top K))
    (ENNReal.inv_ne_top.mpr (bodyVolume_pos K).ne')).mpr
  exact ContinuousOn.integrableOn_compact K.body.isCompact
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).mul
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)).continuousOn

theorem bodyDensity_mul_log {n : ℕ} (K : FullDimensionalBody n) :
    (fun x => bodyDensity K x * Real.log (bodyDensity K x)) =
      (K.body : Set (EuclideanSpace ℝ (Fin n))).indicator
        (fun _ => (volume (K.body : Set (EuclideanSpace ℝ (Fin n))))⁻¹.toReal *
          Real.log (volume (K.body : Set (EuclideanSpace ℝ (Fin n))))⁻¹.toReal) := by
  classical
  funext x
  by_cases hx : x ∈ (K.body : Set (EuclideanSpace ℝ (Fin n))) <;> simp [bodyDensity, hx]

theorem bodyDensity_entropy_integrable {n : ℕ} (K : FullDimensionalBody n) :
    Integrable (fun x => bodyDensity K x * Real.log (bodyDensity K x)) volume := by
  rw [bodyDensity_mul_log]
  exact (integrable_indicator_iff K.body.isCompact.measurableSet).mpr
    (integrableOn_const (bodyVolume_ne_top K))

/-- Uniform bodies embed into the actual law family with all integrals justified. -/
noncomputable def bodyLogConcaveLaw {n : ℕ} (K : FullDimensionalBody n) : LogConcaveLaw n where
  dimension_pos := K.dimension_pos
  law := bodyLaw K
  probability := bodyLaw_probability K
  density := bodyDensity K
  logConcave := bodyDensity_logConcave K
  law_eq := bodyLaw_eq_withDensity K
  moment_one := bodyLaw_integrable_coord K
  moment_two := bodyLaw_integrable_coord_mul K
  entropy_integrable := bodyDensity_entropy_integrable K

/-- The entropy equality uses the integral of the actual normalized density. -/
theorem bodyDensity_entropy {n : ℕ} (K : FullDimensionalBody n) :
    differentialEntropy (bodyDensity K) =
      Real.log (volume (K.body : Set (EuclideanSpace ℝ (Fin n)))).toReal := by
  have hv : (volume (K.body : Set (EuclideanSpace ℝ (Fin n)))).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (bodyVolume_pos K).ne' (bodyVolume_ne_top K))
  rw [differentialEntropy, bodyDensity_mul_log, integral_indicator_const _
    K.body.isCompact.measurableSet]
  simp only [smul_eq_mul, Measure.real, ENNReal.toReal_inv, Real.log_inv]
  field_simp

/-- The body and entropy conventions agree on the actual uniform body law. -/
theorem bodyLogConcaveLaw_isotropicConstant {n : ℕ} (K : FullDimensionalBody n) :
    lawIsotropicConstant (bodyLogConcaveLaw K) = bodyIsotropicConstant K := by
  have hv : 0 < (volume (K.body : Set (EuclideanSpace ℝ (Fin n)))).toReal :=
    ENNReal.toReal_pos (bodyVolume_pos K).ne' (bodyVolume_ne_top K)
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast K.dimension_pos.ne'
  have hd : 0 ≤ (covarianceMatrix (bodyLaw K)).det :=
    covarianceMatrix_det_nonneg (bodyLogConcaveLaw K)
  simp only [lawIsotropicConstant, bodyLogConcaveLaw, bodyDensity_entropy,
    bodyIsotropicConstant, Real.rpow_eq_pow]
  rw [Real.div_rpow hd (sq_nonneg _), ← Real.rpow_natCast_mul hv.le]
  simp only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (1 / (2 * (n : ℝ))) = 1 / (n : ℝ) by field_simp]
  rw [Real.rpow_def_of_pos hv]
  have he : -Real.log (volume (K.body : Set (EuclideanSpace ℝ (Fin n)))).toReal /
      (n : ℝ) = -(Real.log (volume (K.body : Set (EuclideanSpace ℝ (Fin n)))).toReal *
        (1 / (n : ℝ))) := by ring
  rw [he, Real.exp_neg, div_eq_mul_inv]
  ring

/-- The embedding uses actual body laws and the proved equality of conventions. -/
theorem dimensionBodySupremum_le_lawSupremum (n : ℕ) :
    dimensionBodySupremum n ≤ dimensionLawSupremum n := by
  apply iSup_le
  intro K
  rw [← bodyLogConcaveLaw_isotropicConstant K]
  exact lawIsotropicConstant_le_dimensionSupremum (bodyLogConcaveLaw K)

theorem bodySupremum_le_fullDimensionalLawSupremum :
    bodySupremum ≤ fullDimensionalLawSupremum := by
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  exact (dimensionBodySupremum_le_lawSupremum n).trans
    (dimensionLawSupremum_le_fullSupremum hn)

end MathlibExt.Probability.IsotropicConstant

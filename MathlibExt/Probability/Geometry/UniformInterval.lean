/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.LogConcaveUniform
public import Mathlib.Tactic.FieldSimp

/-!
# A positive-dimensional isotropic uniform law

Source: `constants/20a.md` and `constants/20b.md`, the actual uniform cube
example. In dimension one its isotropic dilation is [-√3, √3].
-/

@[expose] public section

namespace MathlibExt.Probability.ThinShell

open MeasureTheory
open scoped ENNReal

/-- **Identification of the line with one-dimensional Euclidean space.** The linear isometric
isomorphism from $\mathbb{R}$ onto one-dimensional Euclidean space $\mathbb{R}^1$ that sends a
real number $x$ to the vector whose only coordinate is $x$. -/
noncomputable def lineIsometry : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

@[simp] theorem lineIsometry_apply (x : ℝ) (i : Fin 1) : lineIsometry x i = x :=
  OrthonormalBasis.singleton_repr x i

/-- **Symmetric interval in one-dimensional Euclidean space.** For a real number $a$, the set of
points of one-dimensional Euclidean space $\mathbb{R}^1$ whose only coordinate lies in the closed
interval $[-a, a]$. It is empty when $a < 0$. -/
def symmetricInterval (a : ℝ) : Set (EuclideanSpace ℝ (Fin 1)) :=
  lineIsometry.symm ⁻¹' Set.Icc (-a) a

theorem symmetricInterval_measurable (a : ℝ) : MeasurableSet (symmetricInterval a) :=
  measurableSet_Icc.preimage lineIsometry.symm.continuous.measurable

theorem symmetricInterval_convex (a : ℝ) : Convex ℝ (symmetricInterval a) :=
  (convex_Icc (-a) a).linear_preimage lineIsometry.symm.toLinearMap

@[simp] theorem lineIsometry_preimage_symmetricInterval (a : ℝ) :
    lineIsometry ⁻¹' symmetricInterval a = Set.Icc (-a) a := by
  ext x
  simp [symmetricInterval]

theorem symmetricInterval_volume (a : ℝ) : volume (symmetricInterval a) =
    ENNReal.ofReal (2 * a) := by
  rw [← lineIsometry.measurePreserving.measure_preimage
    (symmetricInterval_measurable a).nullMeasurableSet]
  rw [lineIsometry_preimage_symmetricInterval, Real.volume_Icc]
  congr 1
  ring

/-- **Uniform distribution on a symmetric interval.** For a real number $a$, the measure on
one-dimensional Euclidean space $\mathbb{R}^1$ obtained by conditioning Lebesgue measure on the
set $\{x : -a \le x_1 \le a\}$ of points whose only coordinate $x_1$ lies in $[-a, a]$, that is,
Lebesgue measure restricted to this set and divided by its measure. For $a > 0$ this is the
uniform probability distribution with density $1/(2a)$ on the interval; for $a \le 0$ the set has
measure zero and the conditioned measure is the zero measure.

It is conditioned Lebesgue measure, not a discrete uniform measure. -/
noncomputable def uniformInterval (a : ℝ) : Measure (EuclideanSpace ℝ (Fin 1)) :=
  ProbabilityTheory.cond volume (symmetricInterval a)

theorem uniformInterval_probability {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (uniformInterval a) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [symmetricInterval_volume]
    exact ne_of_gt (by positivity)
  · rw [symmetricInterval_volume]
    exact ENNReal.ofReal_ne_top

theorem lineIsometry_uniformInterval (a : ℝ) : MeasurePreserving lineIsometry
    (ProbabilityTheory.cond volume (Set.Icc (-a) a)) (uniformInterval a) := by
  have h := (lineIsometry.measurePreserving.restrict_preimage_emb
    lineIsometry.toHomeomorph.measurableEmbedding (symmetricInterval a)).smul_measure
    (volume (symmetricInterval a))⁻¹
  simpa only [lineIsometry_preimage_symmetricInterval, symmetricInterval_volume,
    Real.volume_Icc, show a - -a = 2 * a by ring, ProbabilityTheory.cond,
    uniformInterval] using h

theorem integral_coord_uniformInterval (a : ℝ) (i : Fin 1) :
    (∫ x, x i ∂uniformInterval a) =
      ∫ x : ℝ, x ∂ProbabilityTheory.cond volume (Set.Icc (-a) a) := by
  have h := (lineIsometry_uniformInterval a).integral_comp
    lineIsometry.toHomeomorph.measurableEmbedding (fun x => x i)
  simpa only [lineIsometry_apply] using h.symm

theorem uniformInterval_mean {a : ℝ} (ha : 0 ≤ a) (i : Fin 1) :
    (∫ x, x i ∂uniformInterval a) = 0 := by
  rw [integral_coord_uniformInterval, ProbabilityTheory.cond, integral_smul_measure,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    integral_id]
  simp

theorem uniformInterval_integrable_coord {a : ℝ} (ha : 0 < a) (i : Fin 1) :
    Integrable (fun x => x i) (uniformInterval a) := by
  have hn : (volume (Set.Icc (-a) a) : ℝ≥0∞) ≠ 0 := by
    rw [Real.volume_Icc]
    rw [show a - -a = 2 * a by ring]
    exact ne_of_gt (by positivity)
  have ht : (volume (Set.Icc (-a) a) : ℝ≥0∞) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  apply ((lineIsometry_uniformInterval a).integrable_comp_emb
    lineIsometry.toHomeomorph.measurableEmbedding).mp
  simpa only [Function.comp_def, lineIsometry_apply, ProbabilityTheory.cond] using
    (integrable_smul_measure (ENNReal.inv_ne_zero.mpr ht)
      (ENNReal.inv_ne_top.mpr hn)).mpr
      (show Integrable (fun x : ℝ => x) (volume.restrict (Set.Icc (-a) a)) from
        continuous_id.integrableOn_Icc)

theorem integral_coord_sq_uniformInterval (a : ℝ) (i j : Fin 1) :
    (∫ x, x i * x j ∂uniformInterval a) =
      ∫ x : ℝ, x ^ 2 ∂ProbabilityTheory.cond volume (Set.Icc (-a) a) := by
  have h := (lineIsometry_uniformInterval a).integral_comp
    lineIsometry.toHomeomorph.measurableEmbedding (fun x => x i * x j)
  simpa only [lineIsometry_apply, pow_two] using h.symm

theorem uniformInterval_secondMoment {a : ℝ} (ha : 0 < a) (i j : Fin 1) :
    (∫ x, x i * x j ∂uniformInterval a) = a ^ 2 / 3 := by
  rw [integral_coord_sq_uniformInterval, ProbabilityTheory.cond, integral_smul_measure,
    Real.volume_Icc, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    integral_pow]
  simp only [smul_eq_mul]
  norm_num
  field_simp [show a - -a ≠ 0 by linarith]
  ring

theorem uniformInterval_integrable_coord_mul {a : ℝ} (ha : 0 < a) (i j : Fin 1) :
    Integrable (fun x => x i * x j) (uniformInterval a) := by
  have hn : (volume (Set.Icc (-a) a) : ℝ≥0∞) ≠ 0 := by
    rw [Real.volume_Icc]
    rw [show a - -a = 2 * a by ring]
    exact ne_of_gt (by positivity)
  have ht : (volume (Set.Icc (-a) a) : ℝ≥0∞) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  apply ((lineIsometry_uniformInterval a).integrable_comp_emb
    lineIsometry.toHomeomorph.measurableEmbedding).mp
  simpa only [Function.comp_def, lineIsometry_apply, ProbabilityTheory.cond, pow_two] using
    (integrable_smul_measure (ENNReal.inv_ne_zero.mpr ht)
      (ENNReal.inv_ne_top.mpr hn)).mpr
      (show Integrable (fun x : ℝ => x ^ 2) (volume.restrict (Set.Icc (-a) a)) from
        (continuous_id.pow 2).integrableOn_Icc)

theorem uniformInterval_logConcave {a : ℝ} (ha : 0 < a) :
    IsLogConcaveDensity ((symmetricInterval a).indicator
      (fun _ => (volume (symmetricInterval a))⁻¹.toReal)) := by
  apply isLogConcaveDensity_indicator_const
    (symmetricInterval_convex a) (symmetricInterval_measurable a)
  rw [symmetricInterval_volume, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity)]
  positivity

/-- **The uniform law on [−√3, √3] is isotropic log-concave.** The uniform distribution on the
symmetric interval $[-\sqrt{3}, \sqrt{3}]$ of one-dimensional Euclidean space $\mathbb{R}^1$ is
an isotropic log-concave probability measure: it has a log-concave density with respect to
Lebesgue measure, mean zero and identity covariance.

Source: the one-dimensional isotropic cube, uniform on [-√3, √3]. -/
theorem uniformInterval_sqrt_three_isIsotropicLogConcave :
    IsIsotropicLogConcave (uniformInterval (Real.sqrt 3)) := by
  have ha : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hv : volume (symmetricInterval (Real.sqrt 3)) ≠ 0 := by
    rw [symmetricInterval_volume]
    exact ne_of_gt (by positivity)
  refine ⟨uniformInterval_probability ha,
    ⟨_, uniformInterval_logConcave ha,
      cond_eq_withDensity_indicator volume (symmetricInterval_measurable _) hv⟩,
    ?_, ?_⟩
  · intro i
    exact ⟨uniformInterval_integrable_coord ha i, uniformInterval_mean ha.le i⟩
  · intro i j
    refine ⟨uniformInterval_integrable_coord_mul ha i j, ?_⟩
    rw [uniformInterval_secondMoment ha, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
    simp [Subsingleton.elim i j]

/-- **Thin-shell variance bound for the uniform law on [−√3, √3].** Let $\mu$ be the uniform
distribution on the symmetric interval $[-\sqrt{3}, \sqrt{3}]$ of one-dimensional Euclidean
space $\mathbb{R}^1$. Its normalized radius variance $\int (\|x\|^2 - 1)^2 \, d\mu(x)$ is at most
the thin-shell variance constant, the supremum of the normalized radius variance over all
isotropic log-concave probability measures in all positive dimensions. -/
theorem uniformInterval_variance_le_thinShellConstant :
    normalizedRadiusVariance (uniformInterval (Real.sqrt 3)) ≤ thinShellVarianceConstant :=
  normalizedRadiusVariance_le_constant (by decide)
    uniformInterval_sqrt_three_isIsotropicLogConcave

/-- **Radius fluctuation of the uniform law on [−√3, √3].** Let $\mu$ be the uniform distribution
on the symmetric interval $[-\sqrt{3}, \sqrt{3}]$ of one-dimensional Euclidean space
$\mathbb{R}^1$. Then $\int (\|x\| - \sqrt{1})^2 \, d\mu(x)$, the mean squared deviation of the
Euclidean norm from $\sqrt{1} = 1$, is at most the thin-shell variance constant. -/
theorem uniformInterval_radiusFluctuation_le_thinShellConstant :
    (∫⁻ x, ENNReal.ofReal ((‖x‖ - Real.sqrt (1 : ℝ)) ^ 2)
      ∂uniformInterval (Real.sqrt 3)) ≤ thinShellVarianceConstant :=
    (by simpa only [Nat.cast_one] using
      radius_fluctuation_le_constant (by decide) uniformInterval_sqrt_three_isIsotropicLogConcave)

/-- **The uniform law on [−1, 1] is not isotropic log-concave.** The uniform distribution on the
symmetric interval $[-1, 1]$ of one-dimensional Euclidean space $\mathbb{R}^1$ is not an isotropic
log-concave probability measure.

Its second moment is $1/3$ rather than $1$. -/
theorem uniformInterval_one_not_isIsotropicLogConcave :
    ¬ IsIsotropicLogConcave (uniformInterval 1) := by
  intro h
  have hm : (∫ x, x (0 : Fin 1) * x 0 ∂uniformInterval 1) = 1 := by
    simpa using (h.2.2.2 0 0).2
  rw [uniformInterval_secondMoment (by norm_num : 0 < (1 : ℝ))] at hm
  norm_num at hm

end MathlibExt.Probability.ThinShell

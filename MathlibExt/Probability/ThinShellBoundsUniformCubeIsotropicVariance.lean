/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.ThinShell
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Uniform

import MathlibExt.Probability.Geometry.LogConcaveUniform
import MathlibExt.Probability.Geometry.UniformInterval
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.FieldSimp

/-!
# The isotropic cube's normalized radius variance

The uniform law on the cube with side length `2 * Real.sqrt 3` is isotropic log-concave
and has normalized radius variance `4 / 5` in every positive dimension.

Reference: B. Klartag and J. Lehec, *Thin-shell bounds via parallel coupling*,
arXiv:2507.15495v1 (2025), Introduction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory WithLp
open scoped ENNReal ProbabilityTheory

namespace MathlibExt.Probability.ThinShell

private def cubeSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i : Fin n, |x i| ≤ Real.sqrt 3}

private noncomputable def intervalLaw : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (-Real.sqrt 3) (Real.sqrt 3))

private instance intervalLaw_probability : IsProbabilityMeasure intervalLaw := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc, show Real.sqrt (3 : ℝ) - -Real.sqrt 3 = 2 * Real.sqrt 3 by ring]
    exact ne_of_gt (by positivity)
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

private lemma cubeSet_measurable (n : ℕ) : MeasurableSet (cubeSet n) := by
  have h : MeasurableSet (⋂ i : Fin n,
      {x : EuclideanSpace ℝ (Fin n) | |x i| ≤ Real.sqrt 3}) :=
    MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const
  simpa only [cubeSet, Set.iInter_ofPred] using h

private lemma cubeSet_convex (n : ℕ) : Convex ℝ (cubeSet n) := by
  intro x hx y hy a b ha hb hab i
  change |a * x i + b * y i| ≤ Real.sqrt 3
  calc
    |a * x i + b * y i| ≤ a * |x i| + b * |y i| := by
      simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x i) (b * y i)
    _ ≤ a * Real.sqrt 3 + b * Real.sqrt 3 :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = Real.sqrt 3 := by rw [← add_mul, hab, one_mul]

private lemma cubeSet_preimage (n : ℕ) :
    toLp 2 ⁻¹' cubeSet n = Set.univ.pi (fun _ : Fin n =>
      Set.Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)) := by
  ext x
  simp [cubeSet, abs_le, Pi.le_def, forall_and]

private lemma cubeSet_volume (n : ℕ) :
    volume (cubeSet n) = ENNReal.ofReal (2 * Real.sqrt 3) ^ n := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (cubeSet_measurable n).nullMeasurableSet, cubeSet_preimage, volume_pi_pi]
  simp [Real.volume_Icc, ← two_mul]

private lemma pi_intervalLaw (n : ℕ) :
    Measure.pi (fun _ : Fin n => intervalLaw) = ProbabilityTheory.cond
      volume (Set.univ.pi (fun _ : Fin n => Set.Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3))) := by
  apply Measure.pi_eq
  intro s hs
  simp only [ProbabilityTheory.cond, smul_apply,
    Measure.restrict_apply (MeasurableSet.univ_pi hs), ← Set.pi_inter_distrib,
    volume_pi_pi, intervalLaw, Measure.restrict_apply (hs _), smul_eq_mul,
    Finset.prod_mul_distrib]
  congr 1
  rw [ENNReal.prod_inv_distrib]
  intro i hi j hj hij
  right
  simp [Real.volume_Icc]

private noncomputable def cubeLaw (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  ProbabilityTheory.cond volume (cubeSet n)

private lemma cubeLaw_product (n : ℕ) : MeasurePreserving (toLp 2)
    (Measure.pi (fun _ : Fin n => intervalLaw)) (cubeLaw n) := by
  have hv := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (cubeSet_measurable n).nullMeasurableSet
  have h := ((PiLp.volume_preserving_toLp (Fin n)).restrict_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding (cubeSet n)).smul_measure
    (volume (cubeSet n))⁻¹
  rw [pi_intervalLaw, ProbabilityTheory.cond, cubeLaw, ProbabilityTheory.cond,
    ← cubeSet_preimage, hv]
  exact h

private instance cubeLaw_probability (n : ℕ) : IsProbabilityMeasure (cubeLaw n) := by
  rw [← (cubeLaw_product n).map_eq]
  infer_instance

private lemma intervalLaw_integrable_pow (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) intervalLaw := by
  have h : Integrable (fun x : ℝ => x ^ k)
      (volume.restrict (Set.Icc (-Real.sqrt 3) (Real.sqrt 3))) :=
    (continuous_id.pow k).integrableOn_Icc
  unfold intervalLaw ProbabilityTheory.cond
  apply h.smul_measure
  apply ENNReal.inv_ne_top.mpr
  rw [Real.volume_Icc, show Real.sqrt (3 : ℝ) - -Real.sqrt 3 = 2 * Real.sqrt 3 by ring]
  positivity

private lemma integral_intervalLaw : (∫ x : ℝ, x ∂intervalLaw) = 0 := by
  rw [intervalLaw, ← integral_coord_uniformInterval (Real.sqrt 3) 0]
  exact uniformInterval_mean (by positivity) 0

private lemma integral_sq_intervalLaw : (∫ x : ℝ, x ^ 2 ∂intervalLaw) = 1 := by
  rw [intervalLaw, ← integral_coord_sq_uniformInterval (Real.sqrt 3) 0 0,
    uniformInterval_secondMoment (by positivity), Real.sq_sqrt (by norm_num)]
  norm_num

private lemma integral_fourth_intervalLaw : (∫ x : ℝ, x ^ 4 ∂intervalLaw) = 9 / 5 := by
  have ha : 0 < Real.sqrt (3 : ℝ) := by positivity
  have h5 : Real.sqrt (3 : ℝ) ^ 5 = 9 * Real.sqrt 3 := by
    calc
      Real.sqrt (3 : ℝ) ^ 5 = (Real.sqrt 3 ^ 2) ^ 2 * Real.sqrt 3 := by ring
      _ = 9 * Real.sqrt 3 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  rw [intervalLaw, ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_pow]
  norm_num [h5]
  field_simp [show Real.sqrt (3 : ℝ) - -Real.sqrt 3 ≠ 0 by linarith]
  rw [show Real.sqrt (3 : ℝ) ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 by ring,
    Real.sq_sqrt (by norm_num)]
  norm_num

private lemma memLp_intervalLaw : MemLp (fun x : ℝ => x) 2 intervalLaw := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  exact intervalLaw_integrable_pow 2

private lemma memLp_sq_intervalLaw : MemLp (fun x : ℝ => x ^ 2) 2 intervalLaw := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  simpa only [← pow_mul] using intervalLaw_integrable_pow 4

private lemma variance_sq_intervalLaw : Var[fun x : ℝ => x ^ 2; intervalLaw] = 4 / 5 := by
  rw [variance_eq_sub memLp_sq_intervalLaw]
  change (∫ x : ℝ, (x ^ 2) ^ 2 ∂intervalLaw) - (∫ x : ℝ, x ^ 2 ∂intervalLaw) ^ 2 = 4 / 5
  norm_num [← pow_mul, integral_fourth_intervalLaw, integral_sq_intervalLaw]

private lemma cubeLaw_eval {n : ℕ} (i : Fin n) :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin n) => x i) (cubeLaw n) intervalLaw := by
  have h : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℝ))
      (Measure.pi (fun _ : Fin n => intervalLaw)) (cubeLaw n) := cubeLaw_product n
  exact (measurePreserving_eval (fun _ : Fin n => intervalLaw) i).comp h.symm

private lemma cubeLaw_coordinate_memLp {n : ℕ} (i : Fin n) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (cubeLaw n) :=
  memLp_intervalLaw.comp_measurePreserving (cubeLaw_eval i)

private lemma integral_cubeLaw_eval {n : ℕ} (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i ∂cubeLaw n) = 0 := by
  rw [← integral_intervalLaw, ← (cubeLaw_eval i).map_eq, integral_map]
  all_goals fun_prop

private lemma integral_cubeLaw_coordinate_mul {n : ℕ} (i j : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂cubeLaw n) =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    simp only [← pow_two]
    rw [← integral_sq_intervalLaw, ← (cubeLaw_eval i).map_eq, integral_map]
    all_goals fun_prop
  · rw [ite_eq_right hij, ← (cubeLaw_product n).map_eq, integral_map (by fun_prop) (by fun_prop)]
    have h := (iIndepFun_pi (μ := fun _ : Fin n => intervalLaw)
      (X := fun (_ : Fin n) (x : ℝ) => x) (fun _ => by fun_prop)).indepFun hij
    change (∫ x : Fin n → ℝ, x i * x j ∂Measure.pi (fun _ => intervalLaw)) = 0
    rw [h.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable,
      integral_eval, integral_eval, integral_intervalLaw, zero_mul]

private lemma memLp_norm_sq_cubeLaw (n : ℕ) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) 2 (cubeLaw n) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact memLp_finsetSum _ fun i _ =>
    memLp_sq_intervalLaw.comp_measurePreserving (cubeLaw_eval i)

private lemma integral_norm_sq_cubeLaw (n : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 ∂cubeLaw n) = n := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · calc
      _ = ∑ _i : Fin n, (1 : ℝ) := Finset.sum_congr rfl fun i _ => by
        rw [← integral_sq_intervalLaw, ← (cubeLaw_eval i).map_eq, integral_map]
        all_goals fun_prop
      _ = n := by simp
  · exact fun i _ => (cubeLaw_coordinate_memLp i).integrable_sq

private lemma variance_norm_sq_cubeLaw (n : ℕ) :
    Var[fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2; cubeLaw n] = (4 / 5) * (n : ℝ) := by
  rw [← (cubeLaw_product n).map_eq, variance_map (by fun_prop) (by fun_prop)]
  have h : (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ∘ toLp 2 =
      ∑ i : Fin n, fun x : Fin n → ℝ => x i ^ 2 := by
    ext x
    simp [EuclideanSpace.real_norm_sq_eq]
  rw [h, variance_sum_pi (X := fun (_ : Fin n) (x : ℝ) => x ^ 2)
    (fun _ => memLp_sq_intervalLaw)]
  simp [variance_sq_intervalLaw, mul_comm]

private lemma evariance_norm_sq_cubeLaw (n : ℕ) :
    (∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((‖x‖ ^ 2 - (n : ℝ)) ^ 2)
      ∂cubeLaw n) = ENNReal.ofReal (4 / 5) * (n : ℝ≥0∞) := by
  rw [← integral_norm_sq_cubeLaw n, ← evariance_eq_lintegral_ofReal,
    ← ofReal_variance (memLp_norm_sq_cubeLaw n), variance_norm_sq_cubeLaw,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]

/-- **The isotropic cube has normalized radius variance 4/5.** For every dimension $n \ge 1$, let
$\mu$ be the uniform probability measure on the cube $[-\sqrt{3}, \sqrt{3}]^n \subset \mathbb{R}^n$
(Lebesgue measure restricted to the cube and divided by its volume). Then $\mu$ is isotropic
log-concave (a probability measure with a log-concave Lebesgue density, mean $0$ and identity
covariance), and its normalized radius variance $\frac{1}{n} \int (|x|^2 - n)^2 \, d\mu(x)$
equals $4/5$.

The cube is scaled to covariance identity, so this is the unit-variance convention.
Source: Klartag--Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem uniformCube_isotropic_variance (n : ℕ) (hn : 0 < n) :
    let μ := ProbabilityTheory.cond
      (volume : Measure (EuclideanSpace ℝ (Fin n)))
      {x | ∀ i : Fin n, |x i| ≤ Real.sqrt 3}
    IsIsotropicLogConcave μ ∧ normalizedRadiusVariance μ = ENNReal.ofReal (4 / 5)
    := by
  change IsIsotropicLogConcave (cubeLaw n) ∧
    normalizedRadiusVariance (cubeLaw n) = ENNReal.ofReal (4 / 5)
  have hv₀ : volume (cubeSet n) ≠ 0 := by rw [cubeSet_volume]; positivity
  have hv₁ : volume (cubeSet n) ≠ ⊤ := by rw [cubeSet_volume]; finiteness
  refine ⟨⟨inferInstance, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨(cubeSet n).indicator (fun _ => (volume (cubeSet n))⁻¹.toReal), ?_,
      cond_eq_withDensity_indicator volume (cubeSet_measurable n) hv₀⟩
    exact isLogConcaveDensity_indicator_const (cubeSet_convex n) (cubeSet_measurable n)
      (ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hv₁) (ENNReal.inv_ne_top.mpr hv₀))
  · intro i
    exact ⟨(cubeLaw_coordinate_memLp i).integrable (by norm_num), integral_cubeLaw_eval i⟩
  · intro i j
    exact ⟨(cubeLaw_coordinate_memLp i).integrable_mul (cubeLaw_coordinate_memLp j),
      integral_cubeLaw_coordinate_mul i j⟩
  · rw [normalizedRadiusVariance, evariance_norm_sq_cubeLaw]
    exact ENNReal.mul_div_cancel_right (by exact_mod_cast hn.ne') (by simp)

end MathlibExt.Probability.ThinShell

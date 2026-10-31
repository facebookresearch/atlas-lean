/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.DistributionOfFitnessEffects

/-!
# Tests for the distribution of fitness effects and the Poisson likelihood

Point-mass and mixture DFEs at the neutral spectrum `θ / i`, the gamma DFE as a probability law
(non-vacuity), its mean and variance, the fraction of mutations with `Ns < -1` (`σ < -2`), the
exponential (shape `1`) tail, the Poisson likelihood of a concrete count vector, the profile
maximum in `θ`, and the junk value of the log-likelihood at a zero mean.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace MathlibExtTest.Biology.PopulationGenetics.DistributionOfFitnessEffects

open MathlibExt.Biology.PopulationGenetics.Diffusion
open MathlibExt.Biology.PopulationGenetics.DistributionOfFitnessEffects

/-- A neutral point-mass DFE gives the neutral spectrum `θ / i`. -/
example (θ : ℝ) : dfeSFS (Measure.dirac 0) θ 10 3 = θ / 3 := by
  rw [dfeSFS_dirac, expectedSFS_neutral θ (by norm_num) (by norm_num)]
  norm_num

/-- A half-and-half mixture of a neutral point mass and the selection coefficient `σ`
gives the average of the two spectra. -/
example (θ σ : ℝ) :
    dfeSFS ((1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac σ) θ 10 3 =
      θ / 6 + expectedSFS θ σ 10 3 / 2 := by
  have := Measure.smul_finite (Measure.dirac (0 : ℝ)) (c := 1 / 2) (by simp)
  have := Measure.smul_finite (Measure.dirac σ) (c := 1 / 2) (by simp)
  rw [dfeSFS_add_measure _ _ θ (by norm_num) (by norm_num), dfeSFS_smul_measure,
    dfeSFS_smul_measure, dfeSFS_dirac, dfeSFS_dirac,
    expectedSFS_neutral θ (by norm_num) (by norm_num)]
  norm_num
  ring

/-- The mixture identity at a point-mass DFE. -/
example (θ σ : ℝ) :
    expectedSFS θ σ 5 2 =
      ∫ x in (0 : ℝ)..1, ((5 : ℕ).choose 2 : ℝ) * x ^ 2 * (1 - x) ^ (5 - 2) *
        dfeDensity (Measure.dirac σ) θ x := by
  rw [← dfeSFS_dirac σ θ 5 2]
  exact dfeSFS_eq_integral_dfeDensity _ θ (by norm_num) (by norm_num)

/-- Non-vacuity: the gamma DFE with the shape `0.184` estimated by Boyko et al. is a probability
law. -/
example : IsProbabilityMeasure (gammaDFE 0.184 1) :=
  isProbabilityMeasure_gammaDFE (by norm_num) (by norm_num)

/-- Mean and variance of the gamma DFE with shape `2` and rate `1 / 5` (mean strength `10`). -/
example : ∫ σ, σ ∂gammaDFE 2 (1 / 5) = -10 ∧ variance id (gammaDFE 2 (1 / 5)) = 50 := by
  rw [integral_id_gammaDFE (by norm_num) (by norm_num),
    variance_id_gammaDFE (by norm_num) (by norm_num)]
  norm_num

/-- Under the gamma DFE no mutation is beneficial. -/
example : gammaDFE 0.184 1 (Ioi 0) = 0 := gammaDFE_Ioi_zero _ _

/-- The fraction of new mutations with `N s < -1`, i.e. `σ = 2Ns < -2`. -/
example {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (gammaDFE a r).real (Iio (-2)) = upperIncompleteGamma a (r * 2) / Gamma a :=
  gammaDFE_real_Iio ha hr (by norm_num)

/-- Exponential DFE (shape `1`): the fraction with `σ < -c` is `e^{-r c}`. -/
example {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) : (gammaDFE 1 r).real (Iio (-c)) = exp (-(r * c)) := by
  rw [gammaDFE_real_Iio one_pos hr hc, upperIncompleteGamma_one, Gamma_one, div_one]

/-- The fraction in the band `1 < -σ ≤ 10` under the exponential DFE of rate `1`. -/
example : (gammaDFE 1 1).real (Ico (-10) (-1)) = exp (-1) - exp (-10) := by
  rw [gammaDFE_real_Ico one_pos one_pos (by norm_num) (by norm_num), upperIncompleteGamma_one,
    upperIncompleteGamma_one, Gamma_one, div_one]
  norm_num

/-- Rescaling: a gamma DFE of `s` with rate `1000` is a gamma DFE of `σ = 2Ns` with rate
`1000 / (2N)`; here `2N = 20000`. -/
example : (gammaDFE 0.2 1000).map (fun s => 20000 * s) = gammaDFE 0.2 (1000 / 20000) :=
  gammaDFE_map_const_mul (by norm_num) (by norm_num) (by norm_num)

/-- The joint law of one Poisson count of mean `1` gives the count `0` the probability `e^{-1}`. -/
example : (Measure.pi fun _ : Unit => poissonMeasure 1).real {fun _ => 0} = exp (-1) := by
  rw [pi_poissonMeasure_real_singleton]
  simp

/-- The log-likelihood of counts `(2, 0)` at means `(1, 1)` is `-2 - log 2`. -/
example : poissonLogLik (fun _ : Fin 2 => (1 : ℝ)) ![2, 0] = -2 - log 2 := by
  simp [poissonLogLik, Fin.sum_univ_two]

/-- Junk value outside the domain: at a zero mean, `log 0 = 0` makes a count of `1` cost
nothing, although its probability is `0`. -/
example : poissonLogLik (fun _ : Unit => (0 : ℝ)) (fun _ => 1) = 0 := by
  simp [poissonLogLik]

/-- The profile maximum: with shape `f = (1, 1)` and counts `(3, 1)`, `θ̂ = 2` beats `θ = 5`. -/
example :
    poissonLogLik (fun i => (5 : ℝ) * ![1, 1] i) ![3, 1] ≤
      poissonLogLik (fun i => (∑ j, ((![3, 1] : Fin 2 → ℕ) j : ℝ)) /
        (∑ j, (![1, 1] : Fin 2 → ℝ) j) * ![1, 1] i) ![3, 1] :=
  poissonLogLik_le_profile (fun i => by fin_cases i <;> simp) _ (by simp) (by norm_num)

/-- The score equation for a one-parameter model `E_i(ψ) = ψ f_i` at an interior maximum. -/
example {f : Fin 2 → ℝ} (hf : ∀ i, 0 < f i) (k : Fin 2 → ℕ) {ψ : ℝ} (hψ : 0 < ψ)
    (hmax : IsMaxOn (fun φ => poissonLogLik (fun i => φ * f i) k) (Ioi 0) ψ) :
    ∑ i, ((k i : ℝ) / (ψ * f i) - 1) • fderiv ℝ (fun φ => φ * f i) ψ = 0 :=
  score_eq_zero_of_isMaxOn (E := fun i φ => φ * f i) k (Ioi_mem_nhds hψ) hmax
    (fun i => by fun_prop) (fun i => mul_pos hψ (hf i))

end MathlibExtTest.Biology.PopulationGenetics.DistributionOfFitnessEffects

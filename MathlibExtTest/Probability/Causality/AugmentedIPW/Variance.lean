/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.Variance
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for the AIPW variance, variance estimator and Wald interval

* Definitional values of the estimator and the variance estimator, computed from the
  definitions: the empty sample, a single unit, two units, and a sample mixing a treated and a
  control unit (so both residual terms of the score are used).
* Non-vacuity of the coverage theorem: an i.i.d. standard-normal sample (the infinite product
  measure) with the all-treated score `ψ = Y`, where `Var ψ = 1 ≠ 0` and every hypothesis is
  discharged.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.AugmentedIPW.Variance
open MathlibExt.Probability.Statistics.ProcessInference

namespace MathlibExtTest.Probability.Causality.AugmentedIPW.Variance

/-- All-treated score with propensity `1` and zero regressions: `ψ = Y`. Computed from
`aipwScore_of_mem`, not from any result of the module under test. -/
theorem aipwScore_univ_one (x : ℝ) :
    aipwScore Set.univ (fun _ : ℝ => ()) id (fun _ => 1) (fun _ => 0) (fun _ => 0) x = x := by
  rw [aipwScore_of_mem (Set.mem_univ x)]
  simp

/-- The deterministic sample `Oᵢ = i` on a one-point space. -/
noncomputable def O₀ : ℕ → Unit → ℝ := fun i _ => (i : ℝ)

/-- Boundary: the empty sample has estimator `0`. -/
example : aipwEstimator O₀ Set.univ (fun _ : ℝ => ()) id (fun _ _ _ _ => 1) (fun _ _ _ _ => 0)
    (fun _ _ _ _ => 0) 0 () = 0 := by
  simp [aipwEstimator]

/-- Boundary: the empty sample has variance estimate `0`. -/
example : aipwVarianceEstimator O₀ Set.univ (fun _ : ℝ => ()) id (fun _ _ _ _ => 1)
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) 0 () = 0 := by
  simp [aipwVarianceEstimator]

/-- Boundary: a single unit has variance estimate `0`. -/
example : aipwVarianceEstimator O₀ Set.univ (fun _ : ℝ => ()) id (fun _ _ _ _ => 1)
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) 1 () = 0 := by
  simp [aipwVarianceEstimator, aipwEstimator, aipwFittedScore]

/-- Two units with scores `0` and `1`: estimator `1/2`. -/
example : aipwEstimator O₀ Set.univ (fun _ : ℝ => ()) id (fun _ _ _ _ => 1) (fun _ _ _ _ => 0)
    (fun _ _ _ _ => 0) 2 () = 1 / 2 := by
  simp [aipwEstimator, aipwFittedScore, aipwScore_univ_one, O₀, sum_range_succ]

/-- Two units with scores `0` and `1`: variance estimate `((0 - 1/2)² + (1 - 1/2)²) / 2 = 1/4`,
the `1/n` sample variance (not the `1/(n - 1)` one, which would give `1/2`). -/
example : aipwVarianceEstimator O₀ Set.univ (fun _ : ℝ => ()) id (fun _ _ _ _ => 1)
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) 2 () = 1 / 4 := by
  simp [aipwVarianceEstimator, aipwEstimator, aipwFittedScore, aipwScore_univ_one, O₀,
    sum_range_succ]
  norm_num

/-- A treated unit (`Y = 3`, `Oᵢ > 0`) and a control unit (`Y = -1`, `Oᵢ ≤ 0`) with propensity
`1/2`, `m₀ = 0`, `m₁ = 1`: the scores are `1 + (3 - 1) / (1/2) = 5` and
`1 - (-1 - 0) / (1/2) = 3`, so the estimator is `4` and the variance estimate is `1`. -/
example : aipwVarianceEstimator (fun i (_ : Unit) => if i = 0 then (3 : ℝ) else -1)
    {y | 0 < y} (fun _ : ℝ => ()) id (fun _ _ _ _ => 1 / 2) (fun _ _ _ _ => 0)
    (fun _ _ _ _ => 1) 2 () = 1 := by
  have h3 : aipwScore {y : ℝ | 0 < y} (fun _ : ℝ => ()) id (fun _ => 1 / 2) (fun _ => 0)
      (fun _ => 1) 3 = 5 := by
    rw [aipwScore_of_mem (show (3 : ℝ) ∈ {y : ℝ | 0 < y} by norm_num)]
    norm_num
  have h1 : aipwScore {y : ℝ | 0 < y} (fun _ : ℝ => ()) id (fun _ => 1 / 2) (fun _ => 0)
      (fun _ => 1) (-1) = 3 := by
    rw [aipwScore_of_notMem (show (-1 : ℝ) ∉ {y : ℝ | 0 < y} by norm_num)]
    norm_num
  simp only [aipwVarianceEstimator, aipwEstimator, aipwFittedScore, sum_range_succ,
    sum_range_zero, one_ne_zero, ite_false, ite_true, h1]
  rw [h3]
  norm_num

/-! ### Non-vacuity of the coverage theorem -/

/-- The i.i.d. standard-normal sample: coordinates of the infinite product measure. -/
noncomputable abbrev gaussSample : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ => gaussianReal 0 1

/-- **Non-vacuity.** For an i.i.d. `N(0, 1)` sample and the all-treated score `ψ = Y` with
fixed nuisances, every hypothesis of `tendsto_coverage_aipwWaldInterval` holds (in particular
`Var ψ = 1 ≠ 0`), so the Wald interval for `τ = 0` has asymptotic coverage
`P(-z ≤ N(0, 1) ≤ z)`. -/
example (z : ℝ) :
    Tendsto (fun n : ℕ => gaussSample.real {ω | (0 : ℝ) ∈ waldInterval
      (aipwEstimator (fun i ω => ω i) Set.univ (fun _ : ℝ => ()) id (fun _ _ _ _ => 1)
        (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) n ω)
      (√(aipwVarianceEstimator (fun i ω => ω i) Set.univ (fun _ : ℝ => ()) id
        (fun _ _ _ _ => 1) (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) n ω) / √(n : ℝ)) z})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Icc (-z) z))) := by
  have hψ : aipwScore Set.univ (fun _ : ℝ => ()) id (fun _ => 1) (fun _ => 0) (fun _ => 0) =
      id := funext aipwScore_univ_one
  have hlaw : ∀ i, HasLaw (fun ω : ℕ → ℝ => ω i) (gaussianReal 0 1) gaussSample := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have hzero : ∀ (n : ℕ) (i : ℕ) (ω : ℕ → ℝ),
      aipwFittedScore (fun i ω => ω i) Set.univ (fun _ : ℝ => ()) id (fun _ _ _ _ => 1)
        (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) n i ω = ω i := fun _ i ω =>
    aipwScore_univ_one (ω i)
  refine tendsto_coverage_aipwWaldInterval (e := fun _ => 1) (m₀ := fun _ => 0)
    (m₁ := fun _ => 0) ?_ ?_ ?_ hlaw ?_ ?_ ?_ ?_ ?_ z
  · rw [hψ]; exact measurable_id
  · rw [hψ]; exact memLp_id_gaussianReal 2
  · exact iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  · rw [hψ]; exact integral_id_gaussianReal
  · rw [hψ, variance_id_gaussianReal]; norm_num
  · exact fun n i =>
      (measurable_pi_apply i).aemeasurable.congr (ae_of_all _ fun ω => (hzero n i ω).symm)
  · refine (tendstoInMeasure_of_tendsto_ae (f := fun (_ : ℕ) (_ : ℕ → ℝ) => (0 : ℝ))
      (fun _ => aestronglyMeasurable_const) (ae_of_all _ fun _ => tendsto_const_nhds)).congr_left
      fun n => ae_of_all _ fun ω => ?_
    simp [aipwEstimator, aipwFittedScore, aipwScore_univ_one]
  · simp only [hzero, aipwScore_univ_one, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sum_const_zero, mul_zero]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => tendsto_const_nhds)

end MathlibExtTest.Probability.Causality.AugmentedIPW.Variance

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.CrossedRandomEffects
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Crossed and cluster tests

Concrete checks for crossed random effects and the single-cluster design
effect: correlated distinct rows, diagonal covariance when random-effect
variances vanish, and two-observation cluster computations.

Clause mapping: LI03.1 (no independent-trials inference) is witnessed by
correlation (nonzero covariance of distinct rows sharing a participant).
LI03.2 (shared cluster effect) is witnessed by the gap between true and
independent-row variance and the design-effect identity in one cluster.
The random-intercept adapter is exercised through Pseudobulk's
`not_indepFun_sameDonor`: two rows of one cluster are not independent.
-/

open MeasureTheory ProbabilityTheory Matrix MetaMathlibExt
open MathlibExt.Biology.StatisticalGenetics.MixedModel (phenCov)
open MathlibExt.Biology.StatisticalGenetics.CrossedRandomEffects

namespace MathlibExtTest.Biology.StatisticalGenetics.CrossedRandomEffects

public section

/-- Distinct rows sharing a participant are correlated: their covariance
is nonzero. -/
theorem distinct_rows_correlated {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 2 ⊕ Fin 2))
    (ε : Ω → EuclideanSpace ℝ (Fin 2 × Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2 × Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hγl : P.map γ = multivariateGaussian 0
      (crossedCov (Fin 2) (Fin 2) 1 2))
    (hεl : P.map ε = multivariateGaussian 0 ((3 : ℝ) • 1)) :
    cov[fun ω => (toEuclideanLin X β +
        toEuclideanLin (crossedDesign (Fin 2) (Fin 2)) (γ ω) +
        ε ω).ofLp ((0, 0) : Fin 2 × Fin 2),
      fun ω => (toEuclideanLin X β +
        toEuclideanLin (crossedDesign (Fin 2) (Fin 2)) (γ ω) +
        ε ω).ofLp ((0, 1) : Fin 2 × Fin 2); P] = 1 := by
  have h := covariance_crossed_response γ ε hγ hε hind X β 1 2 3
    (by norm_num) (by norm_num) (by norm_num) hγl hεl (0, 0) (0, 1)
  simpa using h

/-- Distinct rows sharing neither participant nor item are uncorrelated:
their covariance is zero. -/
theorem distinct_rows_uncorrelated {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 2 ⊕ Fin 2))
    (ε : Ω → EuclideanSpace ℝ (Fin 2 × Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2 × Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hγl : P.map γ = multivariateGaussian 0
      (crossedCov (Fin 2) (Fin 2) 1 2))
    (hεl : P.map ε = multivariateGaussian 0 ((3 : ℝ) • 1)) :
    cov[fun ω => (toEuclideanLin X β +
        toEuclideanLin (crossedDesign (Fin 2) (Fin 2)) (γ ω) +
        ε ω).ofLp ((0, 0) : Fin 2 × Fin 2),
      fun ω => (toEuclideanLin X β +
        toEuclideanLin (crossedDesign (Fin 2) (Fin 2)) (γ ω) +
        ε ω).ofLp ((1, 1) : Fin 2 × Fin 2); P] = 0 := by
  have h := covariance_crossed_response γ ε hγ hε hind X β 1 2 3
    (by norm_num) (by norm_num) (by norm_num) hγl hεl (0, 0) (1, 1)
  have hp : ((0, 0) : Fin 2 × Fin 2).1 ≠ ((1, 1) : Fin 2 × Fin 2).1 := by
    decide
  have hi : ((0, 0) : Fin 2 × Fin 2).2 ≠ ((1, 1) : Fin 2 × Fin 2).2 := by
    decide
  have hd : ((0, 0) : Fin 2 × Fin 2) ≠ (1, 1) := by decide
  simpa [hp, hi, hd] using h

/-- When both random-effect variances vanish, the crossed `phenCov` is
diagonal. -/
theorem phenCov_diagonal_of_zero_variances (k l : Fin 2 × Fin 2) :
    phenCov (crossedDesign (Fin 2) (Fin 2))
      (crossedCov (Fin 2) (Fin 2) 0 0) ((5 : ℝ) • 1) k l =
      (if k = l then (5 : ℝ) else 0) := by
  rw [phenCov_crossed_apply]
  simp

/-- Two-observation cluster: mean variance is `3 / 2`. -/
theorem cluster_two_obs_mean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hγl : P.map γ = multivariateGaussian 0 ((1 : ℝ) • 1))
    (hεl : P.map ε = multivariateGaussian 0 ((1 : ℝ) • 1)) :
    Var[fun ω => (∑ k, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign 2) (γ ω) + ε ω).ofLp k) / (2 : ℝ);
      P] = 3 / 2 := by
  have h := variance_cluster_mean 2 X β 1 1 (by norm_num) (by norm_num)
    hγl hεl (by norm_num) (γ := γ) (ε := ε) (hγ := hγ) (hε := hε)
    (hind := hind)
  norm_num at h ⊢
  linarith

/-- Two-observation cluster: independent-row variance is below true mean
variance. -/
theorem cluster_two_obs_gap {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hγl : P.map γ = multivariateGaussian 0 ((1 : ℝ) • 1))
    (hεl : P.map ε = multivariateGaussian 0 ((1 : ℝ) • 1))
    (k : Fin 2) :
    Var[fun ω => (toEuclideanLin X β +
      toEuclideanLin (clusterDesign 2) (γ ω) + ε ω).ofLp k; P] / (2 : ℝ) <
      Var[fun ω => (∑ j, (toEuclideanLin X β +
        toEuclideanLin (clusterDesign 2) (γ ω) + ε ω).ofLp j) / (2 : ℝ);
        P] := by
  have h := variance_cluster_row_div_lt_mean 2 X β 1 1 (by norm_num) hγl hεl
    (by norm_num) (by norm_num) k (γ := γ) (ε := ε) (hγ := hγ) (hε := hε)
    (hind := hind)
  exact h

/-- Two-observation cluster: design-effect identity holds (`3 / 2` on both
sides). -/
theorem cluster_two_obs_design_effect {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hγl : P.map γ = multivariateGaussian 0 ((1 : ℝ) • 1))
    (hεl : P.map ε = multivariateGaussian 0 ((1 : ℝ) • 1)) (k : Fin 2) :
    Var[fun ω => (∑ j, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign 2) (γ ω) + ε ω).ofLp j) / (2 : ℝ);
      P] = (1 + ((2 : ℝ) - 1) * (1 / (1 + 1))) *
      (Var[fun ω => (toEuclideanLin X β +
        toEuclideanLin (clusterDesign 2) (γ ω) + ε ω).ofLp k; P] /
        (2 : ℝ)) := by
  have h := variance_cluster_mean_eq_designEffect 2 X β 1 1 (by norm_num)
    (by norm_num) hγl hεl (by norm_num) k (γ := γ) (ε := ε) (hγ := hγ)
    (hε := hε) (hind := hind)
  exact h

/-- Two-observation cluster: mean variance is at least the shared effect. -/
theorem cluster_two_obs_lower_bound {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hγl : P.map γ = multivariateGaussian 0 ((1 : ℝ) • 1))
    (hεl : P.map ε = multivariateGaussian 0 ((1 : ℝ) • 1)) :
    (1 : ℝ) ≤ Var[fun ω => (∑ k, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign 2) (γ ω) + ε ω).ofLp k) / (2 : ℝ);
      P] := by
  have h := le_variance_cluster_mean 2 X β 1 1 (by norm_num) (by norm_num)
    hγl hεl (by norm_num) (γ := γ) (ε := ε) (hγ := hγ) (hε := hε)
    (hind := hind)
  exact h

/-- Through `isRandomIntercept_cluster_response`, Pseudobulk's `not_indepFun_sameDonor`
applies: two rows of one Gaussian cluster with a positive cluster variance are not
independent. -/
theorem cluster_two_obs_not_indep {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hγl : P.map γ = multivariateGaussian 0 ((1 : ℝ) • 1))
    (hεl : P.map ε = multivariateGaussian 0 ((1 : ℝ) • 1)) :
    ¬ IndepFun (fun ω => (toEuclideanLin X β +
        toEuclideanLin (clusterDesign 2) (γ ω) + ε ω).ofLp 0)
      (fun ω => (toEuclideanLin X β +
        toEuclideanLin (clusterDesign 2) (γ ω) + ε ω).ofLp 1) P :=
  MathlibExt.Biology.Omics.Pseudobulk.not_indepFun_sameDonor
    (isRandomIntercept_cluster_response 2 γ ε hγ hε hind X β 1 1 (by norm_num)
      (by norm_num) hγl hεl) one_ne_zero 0 (by decide)

/-- Zero within-cluster variance is allowed: with `σw2 = 0` the mean of a two-observation
cluster has variance `σc2 = 1`; averaging removes nothing. -/
theorem cluster_two_obs_mean_zero_residual {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : Ω → EuclideanSpace ℝ (Fin 1))
    (ε : Ω → EuclideanSpace ℝ (Fin 2))
    (hγ : Measurable γ) (hε : Measurable ε) (hind : IndepFun γ ε P)
    (X : Matrix (Fin 2) (Fin 1) ℝ) (β : EuclideanSpace ℝ (Fin 1))
    (hγl : P.map γ = multivariateGaussian 0 ((1 : ℝ) • 1))
    (hεl : P.map ε = multivariateGaussian 0 ((0 : ℝ) • 1)) :
    Var[fun ω => (∑ k, (toEuclideanLin X β +
      toEuclideanLin (clusterDesign 2) (γ ω) + ε ω).ofLp k) / (2 : ℝ);
      P] = 1 := by
  have h := variance_cluster_mean 2 γ ε hγ hε hind X β 1 0 (by norm_num) le_rfl
    hγl hεl (by norm_num)
  simpa using h

end

end MathlibExtTest.Biology.StatisticalGenetics.CrossedRandomEffects

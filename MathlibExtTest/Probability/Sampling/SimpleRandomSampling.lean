/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Sampling.SimpleRandomSampling
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Field

/-!
# Simple random sampling boundary tests

Boundary values for simple random sampling without replacement.

## Test groups

* Non-vacuity (`N = 3`, `n = 2`, `y = (0, 3, 6)`): the unbiasedness and
  variance identities hold with nonzero values, and the divisor-`N` variance
  gives the wrong answer.
* Census (`n = N = 2`): the randomization expectation evaluates at `univ`,
  the sample mean equals the population mean, and the variance is zero.
* Excluded sample sizes (`n = 0`, `n > N`): unbiasedness fails since the
  expectation is the junk value `0`.
* Correlated clusters on `Fin 4`: equal inclusion probabilities do not imply
  the SRS variance; the cluster design is unbiased but has larger variance.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Sampling

open MathlibExt.Probability.Causality MathlibExt.Probability.Sampling Finset

/-- Non-vacuity: SRS mean is unbiased in the `N = 3`, `n = 2` example. -/
theorem srs_unbiased_example :
    randExp 2 (sampleMean (![(0 : ℝ), 3, 6] : Fin 3 → ℝ)) = 3 := by
  have h :=
    randExp_sampleMean (![(0 : ℝ), 3, 6] : Fin 3 → ℝ) (n := 2) (by norm_num)
      (by simp [Fintype.card_fin])
  have hmean : popMean (![(0 : ℝ), 3, 6] : Fin 3 → ℝ) = 3 := by
    rw [popMean]
    simp [Fin.sum_univ_three, Fintype.card_fin]
    norm_num
  rw [h, hmean]

/-- Non-vacuity: population variance with divisor `N - 1` in the example. -/
theorem srs_popVar_example :
    popVar (![(0 : ℝ), 3, 6] : Fin 3 → ℝ) = 9 := by
  have hmean : popMean (![(0 : ℝ), 3, 6] : Fin 3 → ℝ) = 3 := by
    rw [popMean]
    simp [Fin.sum_univ_three, Fintype.card_fin]
    norm_num
  rw [popVar, hmean]
  simp [Fin.sum_univ_three, Fintype.card_fin]
  norm_num

/-- Non-vacuity: SRS variance identity in the `N = 3`, `n = 2` example. -/
theorem srs_variance_example :
    randExp 2 (fun S =>
      (sampleMean (![(0 : ℝ), 3, 6] : Fin 3 → ℝ) S -
        popMean (![(0 : ℝ), 3, 6])) ^ 2) = 3 / 2 := by
  have hvar : popVar (![(0 : ℝ), 3, 6] : Fin 3 → ℝ) = 9 :=
    srs_popVar_example
  have h :=
    randExp_sq_sampleMean_sub_popMean (![(0 : ℝ), 3, 6] : Fin 3 → ℝ) (n := 2)
      (by norm_num) (by simp [Fintype.card_fin])
  rw [h, hvar]
  simp [Fintype.card_fin]
  norm_num

/-- Non-vacuity: divisor-`N` variance gives `1`, not the correct `3 / 2`. -/
theorem srs_variance_wrong_convention :
    randExp 2 (fun S =>
      (sampleMean (![(0 : ℝ), 3, 6] : Fin 3 → ℝ) S -
        popMean (![(0 : ℝ), 3, 6])) ^ 2) ≠
      (1 - (2 : ℝ) / 3) *
        ((∑ i, ((![(0 : ℝ), 3, 6] : Fin 3 → ℝ) i -
          popMean (![(0 : ℝ), 3, 6])) ^ 2) / 3) / 2 := by
  have hlhs := srs_variance_example
  have hmean : popMean (![(0 : ℝ), 3, 6] : Fin 3 → ℝ) = 3 := by
    rw [popMean]
    simp [Fin.sum_univ_three, Fintype.card_fin]
    norm_num
  have hrhs : (1 - (2 : ℝ) / 3) *
      ((∑ i, ((![(0 : ℝ), 3, 6] : Fin 3 → ℝ) i -
        popMean (![(0 : ℝ), 3, 6])) ^ 2) / 3) / 2 = 1 := by
    rw [hmean]
    simp [Fin.sum_univ_three]
    norm_num
  rw [hlhs, hrhs]
  norm_num

/-- Census: at `n = N = 2` the randomization expectation is evaluation. -/
theorem census_randExp_eq (f : Finset (Fin 2) → ℝ) :
    randExp 2 f = f univ := by
  rw [randExp]
  have hcard : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  rw [hcard]
  have hps : (univ : Finset (Fin 2)).powersetCard 2 = {univ} := by decide
  rw [hps]
  simp

/-- Census: unbiasedness holds with `n = N = 2`. -/
theorem census_unbiased :
    randExp 2 (sampleMean (![(-2 : ℝ), 5] : Fin 2 → ℝ)) = 3 / 2 := by
  have h :=
    randExp_sampleMean (![(-2 : ℝ), 5] : Fin 2 → ℝ) (n := 2) (by norm_num)
      (by simp [Fintype.card_fin])
  have hmean : popMean (![(-2 : ℝ), 5] : Fin 2 → ℝ) = 3 / 2 := by
    rw [popMean]
    simp [Fin.sum_univ_two, Fintype.card_fin]
    norm_num
  rw [h, hmean]

/-- Census: variance is zero with `n = N = 2`. -/
theorem census_variance :
    randExp 2 (fun S =>
      (sampleMean (![(-2 : ℝ), 5] : Fin 2 → ℝ) S -
        popMean (![(-2 : ℝ), 5])) ^ 2) = 0 := by
  have h :=
    randExp_sq_sampleMean_sub_popMean (![(-2 : ℝ), 5] : Fin 2 → ℝ) (n := 2)
      (by norm_num) (by simp [Fintype.card_fin])
  rw [h]
  simp [Fintype.card_fin]

/-- Excluded size: `n = 0` gives junk `0`, not the population mean. -/
theorem zero_sample_not_unbiased :
    randExp 0 (sampleMean (fun _ : Fin 2 => (1 : ℝ))) ≠
      popMean (fun _ : Fin 2 => (1 : ℝ)) := by
  have hlhs : randExp 0 (sampleMean (fun _ : Fin 2 => (1 : ℝ))) = 0 := by
    rw [randExp]
    have hcard : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
    rw [hcard]
    have hps : (univ : Finset (Fin 2)).powersetCard 0 = {∅} := by decide
    rw [hps]
    simp [sampleMean]
  have hrhs : popMean (fun _ : Fin 2 => (1 : ℝ)) = 1 := by
    rw [popMean]
    simp [Fintype.card_fin]
  rw [hlhs, hrhs]
  norm_num

/-- Excluded size: `n = 3 > N = 2` gives junk `0`, not the mean. -/
theorem oversized_sample_not_unbiased :
    randExp 3 (sampleMean (fun _ : Fin 2 => (1 : ℝ))) ≠
      popMean (fun _ : Fin 2 => (1 : ℝ)) := by
  have hlhs : randExp 3 (sampleMean (fun _ : Fin 2 => (1 : ℝ))) = 0 := by
    rw [randExp]
    have hcard : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
    rw [hcard]
    have hps : (univ : Finset (Fin 2)).powersetCard 3 = ∅ := by decide
    rw [hps]
    simp
  have hrhs : popMean (fun _ : Fin 2 => (1 : ℝ)) = 1 := by
    rw [popMean]
    simp [Fintype.card_fin]
  rw [hlhs, hrhs]
  norm_num

/-- Uniform choice of one of the two clusters `{0, 1}` or `{2, 3}`. -/
noncomputable def clusterExp (f : Finset (Fin 4) → ℝ) : ℝ :=
  (f {0, 1} + f {2, 3}) / 2

/-- Clustered outcomes `(1, 1, 0, 0)` on `Fin 4`. -/
def clusterY : Fin 4 → ℝ := ![1, 1, 0, 0]

/-- Clusters: every unit has inclusion probability `1 / 2`. -/
theorem cluster_inclusion (i : Fin 4) :
    clusterExp (fun S => if i ∈ S then (1 : ℝ) else 0) = 1 / 2 := by
  fin_cases i <;> simp [clusterExp]

/-- Clusters: the pair `{0, 2}` never appears together. -/
theorem cluster_pair_inclusion_zero :
    clusterExp (fun S : Finset (Fin 4) =>
      if 0 ∈ S ∧ 2 ∈ S then (1 : ℝ) else 0) = 0 := by
  simp [clusterExp]

/-- Clusters: the cluster design is unbiased for its mean. -/
theorem cluster_unbiased :
    clusterExp (sampleMean clusterY) = popMean clusterY := by
  have h1 : sampleMean clusterY {0, 1} = 1 := by
    rw [sampleMean]
    simp [clusterY]
  have h2 : sampleMean clusterY {2, 3} = 0 := by
    rw [sampleMean]
    simp [clusterY]
  have hmean : popMean clusterY = 1 / 2 := by
    rw [popMean]
    simp [clusterY, Fin.sum_univ_four, Fintype.card_fin]
    norm_num
  simp [clusterExp, h1, h2, hmean]

/-- Clusters: variance under the cluster design is `1 / 4`. -/
theorem cluster_variance :
    clusterExp (fun S => (sampleMean clusterY S - popMean clusterY) ^ 2) =
      1 / 4 := by
  have h1 : sampleMean clusterY {0, 1} = 1 := by
    rw [sampleMean]
    simp [clusterY]
  have h2 : sampleMean clusterY {2, 3} = 0 := by
    rw [sampleMean]
    simp [clusterY]
  have hmean : popMean clusterY = 1 / 2 := by
    rw [popMean]
    simp [clusterY, Fin.sum_univ_four, Fintype.card_fin]
    norm_num
  simp [clusterExp, h1, h2, hmean]
  norm_num

/-- Clusters: SRS variance for `clusterY` with `n = 2` is `1 / 12`. -/
theorem srs_variance_clusterY :
    randExp 2 (fun S => (sampleMean clusterY S - popMean clusterY) ^ 2) =
      1 / 12 := by
  have hvar : popVar clusterY = 1 / 3 := by
    have hmean : popMean clusterY = 1 / 2 := by
      rw [popMean]
      simp [clusterY, Fin.sum_univ_four, Fintype.card_fin]
      norm_num
    rw [popVar, hmean]
    simp [clusterY, Fin.sum_univ_four, Fintype.card_fin]
    norm_num
  have h :=
    randExp_sq_sampleMean_sub_popMean clusterY (n := 2) (by norm_num)
      (by simp [Fintype.card_fin])
  rw [h, hvar]
  simp [Fintype.card_fin]
  norm_num

/-- Clusters: cluster-design variance differs from the SRS variance. -/
theorem cluster_variance_ne_srs :
    clusterExp (fun S => (sampleMean clusterY S - popMean clusterY) ^ 2) ≠
      randExp 2 (fun S => (sampleMean clusterY S - popMean clusterY) ^ 2) := by
  rw [cluster_variance, srs_variance_clusterY]
  norm_num

end MathlibExtTest.Probability.Sampling

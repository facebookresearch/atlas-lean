/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.NormalTheory

/-!
# Tests for `MathlibExt.Probability.Statistics.NormalTheory`

Quantile facts at the Cauchy (`t_1`) and `F(1, 1)` boundary; the `t` median is `0`;
two-sided coverage collapses to `0` at the threshold `c = 0` and for negative `c`; one-sided
coverage at `c = 0` is `1/2`; the exact `95%` two-sided interval at `n = 2`; exact-size
`F` test and `F` region at `(q, n - p) = (1, 1)`.
-/

namespace ProbabilityTheory.NormalTheoryChecks

open MeasureTheory ProbabilityTheory Set

/-- Boundary `k = 1` (Cauchy): the `t` quantile is exact at every level in `(0, 1)`. -/
example {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    cdf (studentTMeasure 1) (cdfQuantile (studentTMeasure 1) u) = u :=
  cdf_studentTMeasure_cdfQuantile one_pos hu

/-- Symmetry pins the median: `F_{t_k}(0) = 1/2` for every `k ≥ 1`. -/
example {k : ℕ} (hk : 0 < k) : cdf (studentTMeasure k) 0 = 1 / 2 := by
  have h := cdf_studentTMeasure_neg hk 0
  rw [neg_zero] at h
  linarith

/-- The `F(1, 1)` cdf is continuous and its quantile is exact. -/
example {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Continuous (cdf (snedecorFMeasure 1 1)) ∧
      cdf (snedecorFMeasure 1 1) (cdfQuantile (snedecorFMeasure 1 1) u) = u :=
  ⟨continuous_cdf_snedecorFMeasure one_pos one_pos,
    cdf_snedecorFMeasure_cdfQuantile one_pos one_pos hu⟩

/-- Degenerate endpoint: with zero degrees of freedom the law is the zero measure, so the
no-atom lemma is trivially true; the `k ≥ 1` hypothesis is needed only for probability. -/
example (x : ℝ) : studentTMeasure 0 {x} = 0 := studentTMeasure_singleton 0 x

/-- Boundary `c = 0`: the zero-width interval covers with probability `0` (no atoms). -/
example {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    P.real {ω | |(∑ i, X ω i) / n - μ| ≤ 0 *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} = 0 := by
  rw [one_sample_t_interval_measureReal_eq hn μ hv 0 hX, neg_zero, Icc_self, measureReal_def,
    studentTMeasure_singleton, ENNReal.toReal_zero]

/-- Boundary `c < 0`: a negative threshold gives an empty interval and coverage `0`. -/
example {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    P.real {ω | |(∑ i, X ω i) / n - μ| ≤ (-1) *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} = 0 := by
  rw [one_sample_t_interval_measureReal_eq hn μ hv (-1) hX, Icc_eq_empty (by norm_num),
    measureReal_empty]

/-- One-sided bounds at `c = 0`: `X̄ ≤ μ` and `μ ≤ X̄` each have probability `1/2`. -/
example {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    P.real {ω | (∑ i, X ω i) / n - 0 *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ) ≤ μ} = 1 / 2 ∧
    P.real {ω | μ ≤ (∑ i, X ω i) / n + 0 *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} = 1 / 2 := by
  have hmed : cdf (studentTMeasure (n - 1)) 0 = 1 / 2 := by
    have h := cdf_studentTMeasure_neg (show 0 < n - 1 by omega) 0
    rw [neg_zero] at h
    linarith
  exact ⟨(one_sample_t_lower_bound_measureReal_eq hn μ hv 0 hX).trans hmed,
    (one_sample_t_upper_bound_measureReal_eq hn μ hv 0 hX).trans hmed⟩

/-- Use case: the textbook `95%` two-sided interval from a sample of size `2` (Cauchy pivot)
has coverage exactly `0.95`. -/
example (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin 2 → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin 2 => gaussianReal μ v) P) :
    P.real {ω | |(∑ i, X ω i) / (2 : ℕ) - μ| ≤
      cdfQuantile (studentTMeasure (2 - 1)) (1 - (1 / 20) / 2) *
        √((∑ i, (X ω i - (∑ j, X ω j) / (2 : ℕ)) ^ 2) / (((2 : ℕ) : ℝ) - 1)) /
          √((2 : ℕ) : ℝ)} = 1 - 1 / 20 :=
  one_sample_t_interval_coverage_eq le_rfl μ hv ⟨by norm_num, by norm_num⟩ hX

/-- Use case: the `95%` one-sided bounds at `n = 3` (`t_2` pivot) are exact. -/
example (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin 3 → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin 3 => gaussianReal μ v) P) :
    P.real {ω | (∑ i, X ω i) / (3 : ℕ) - cdfQuantile (studentTMeasure (3 - 1)) (1 - 1 / 20) *
      √((∑ i, (X ω i - (∑ j, X ω j) / (3 : ℕ)) ^ 2) / (((3 : ℕ) : ℝ) - 1)) /
        √((3 : ℕ) : ℝ) ≤ μ} = 1 - 1 / 20 :=
  (one_sample_t_one_sided_coverage_eq (by norm_num) μ hv ⟨by norm_num, by norm_num⟩ hX).1

end ProbabilityTheory.NormalTheoryChecks

namespace MathlibExt.Probability.Statistics.LinearModel.NormalTheoryChecks

open Matrix MeasureTheory ProbabilityTheory Set MathlibExt.Probability.Statistics.LinearModel

/-- Use case: at `(q, n - p) = (1, 1)` the `5%` `F` test has size exactly `0.05` and the
`95%` `F` region covers `C β` with probability exactly `0.95`. -/
example {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    [Fintype r] [DecidableEq r] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ))
    (hr : Fintype.card r = 1) (hkm : Fintype.card m = Fintype.card k + 1)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    μ.real {ω | cdfQuantile (snedecorFMeasure 1 1) (1 - 1 / 20) <
        fStatistic X C (C *ᵥ β) (X *ᵥ β + ε ω)} = 1 / 20 ∧
    μ.real {ω | C *ᵥ β ∈ {γ : r → ℝ | fStatistic X C γ (X *ᵥ β + ε ω) ≤
        cdfQuantile (snedecorFMeasure 1 1) (1 - 1 / 20)}} = 1 - 1 / 20 := by
  have hr' : 0 < Fintype.card r := by omega
  have hkm' : Fintype.card k < Fintype.card m := by omega
  have h2 : Fintype.card m - Fintype.card k = 1 := by omega
  have hα : (1 / 20 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 := fTest_size_eq hX hC hr' hkm' β rfl hσ hε hα
  have h3 := fConfidenceRegion_coverage_eq hX hC hr' hkm' β hσ hε hα
  rw [hr, h2] at h1 h3
  exact ⟨h1, h3⟩

/-- Every threshold: under `H₀` the rejection probability of `F > c` is the `F` upper tail. -/
example {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    [Fintype r] [DecidableEq r] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) (hr : 0 < Fintype.card r)
    (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    μ.real {ω | 0 < fStatistic X C (C *ᵥ β) (X *ᵥ β + ε ω)} =
      1 - cdf (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)) 0 :=
  fStatistic_measureReal_gt_eq hX hC hr hkm β rfl hσ hε 0

end MathlibExt.Probability.Statistics.LinearModel.NormalTheoryChecks

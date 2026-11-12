/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Inference
public import MathlibExt.Probability.Statistics.LinearModel.LinearHypothesisF
public import MathlibExt.Probability.Quantile
public import MathlibExt.Probability.CdfContinuityPoints

/-!
# Exact normal-theory `t` intervals and `F` tests with proved quantiles

The merged laws `studentTMeasure k` (`MathlibExt/Probability/Distributions/StudentT.lean`) and
`snedecorFMeasure d₁ d₂` (`.../SnedecorF.lean`) have Lebesgue densities, so they have no atoms
and continuous cdfs. Consequently the merged generalized inverse `cdfQuantile`
(`MathlibExt/Probability/Quantile.lean`) is an exact inverse on `(0, 1)`, and Student's `t` cdf
satisfies `F(-x) = 1 - F(x)`. These discharge the quantile hypotheses of the merged
`t`/`F` sampling theorems (`map_tStatistic_pi_gaussianReal`, `hasLaw_fStatistic`) and turn
coverage inequalities into equalities.

## Main results

Quantile existence and continuity (proved, not assumed):
* `continuous_cdf_studentTMeasure`, `cdf_studentTMeasure_neg`,
  `cdf_studentTMeasure_cdfQuantile`: for `k ≥ 1`, `F_{t_k}(cdfQuantile t_k u) = u`, `u ∈ (0,1)`.
* `continuous_cdf_snedecorFMeasure`, `cdf_snedecorFMeasure_cdfQuantile`: same for
  `F(d₁, d₂)`, `d₁, d₂ ≥ 1`.

One-sample `t` (i.i.d. `N(μ, v)`, `n ≥ 2`, `v ≠ 0`, variance unknown, `n - 1` degrees of
freedom, `S² = ∑ (Xᵢ - X̄)² / (n - 1)`):
* `one_sample_t_interval_measureReal_eq`: two-sided, `P(|X̄ - μ| ≤ c S/√n) = t_{n-1}([-c, c])`
  for every real `c`.
* `one_sample_t_lower_bound_measureReal_eq`, `one_sample_t_upper_bound_measureReal_eq`:
  one-sided, both equal `F_{t_{n-1}}(c)` for every real `c`.
* `one_sample_t_interval_coverage_eq`: with `c = cdfQuantile t_{n-1} (1 - α/2)`, two-sided
  coverage is exactly `1 - α`.
* `one_sample_t_one_sided_coverage_eq`: with `c = cdfQuantile t_{n-1} (1 - α)`, each
  one-sided bound has coverage exactly `1 - α`.

Linear-hypothesis `F` (fixed full-rank design, Gaussian errors with unknown `σ`,
`(q, n - p)` degrees of freedom):
* `fStatistic_measureReal_gt_eq`: under `H₀ : C β = γ`, `P(F > c) = 1 - F_{F(q,n-p)}(c)`.
* `fTest_size_eq`: rejecting when `F > cdfQuantile F(q, n-p) (1 - α)` has size exactly `α`.
* `fConfidenceRegion_coverage_eq`: the region `{γ | F(γ) ≤ cdfQuantile F(q, n-p) (1 - α)}`
  covers `C β` with probability exactly `1 - α`.

The known-variance (`z`) interval is not treated here.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Set Real Filter
open scoped Topology ENNReal

/-! ### Quantiles of a law with continuous cdf -/

/-- For a probability measure with continuous cdf, the generalized inverse is an exact
inverse on `(0, 1)`. -/
private theorem cdf_cdfQuantile_of_continuous {μ : Measure ℝ} (hμ : Continuous (cdf μ))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : cdf μ (cdfQuantile μ u) = u := by
  refine le_antisymm ?_ (cdfQuantile_mem μ hu)
  set q := cdfQuantile μ u
  have hlt : ∀ x < q, cdf μ x ≤ u := fun x hx => by
    by_contra h
    exact (not_le.mpr hx) ((cdfQuantile_le_iff μ hu).mpr (not_le.mp h).le)
  have ht : Tendsto (cdf μ) (𝓝[<] q) (𝓝 (cdf μ q)) :=
    hμ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with x hx using hlt x hx)

/-! ### Student's `t` law: no atoms, continuity, symmetry, quantiles -/

/-- Student's `t` law has no atoms. -/
theorem studentTMeasure_singleton (k : ℕ) (x : ℝ) : studentTMeasure k {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- **Continuity of the Student `t` cdf**: for `k ≥ 1` the cdf of `t_k` is continuous. -/
theorem continuous_cdf_studentTMeasure {k : ℕ} (hk : 0 < k) :
    Continuous (cdf (studentTMeasure k)) := by
  have := isProbabilityMeasure_studentTMeasure hk
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rw [MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero]
  exact studentTMeasure_singleton k x

/-- Student's `t` law is symmetric: the left tail at `-x` equals the right tail at `x`. -/
theorem studentTMeasure_Iic_neg (k : ℕ) (x : ℝ) :
    studentTMeasure k (Iic (-x)) = studentTMeasure k (Ici x) := by
  set f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
    (Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) *
      (1 + t ^ 2 / k) ^ (-((k : ℝ) + 1) / 2)) with hf
  have hfm : Measurable f := by fun_prop
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Iic (-x) = Ici x := by
    ext t; simp
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
    (measurableSet_Iic (a := -x)) hfm
  rw [hpre] at h
  have heven : (fun t => f (-t)) = f := by funext t; simp [hf]
  rw [heven] at h
  rw [studentTMeasure, withDensity_apply _ measurableSet_Iic, withDensity_apply _ measurableSet_Ici,
    ← hf, h]

/-- **Symmetry of the Student `t` cdf**: `F(-x) = 1 - F(x)` for `k ≥ 1`. -/
theorem cdf_studentTMeasure_neg {k : ℕ} (hk : 0 < k) (x : ℝ) :
    cdf (studentTMeasure k) (-x) = 1 - cdf (studentTMeasure k) x := by
  have := isProbabilityMeasure_studentTMeasure hk
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, studentTMeasure_Iic_neg, ← measureReal_def,
    ← Ioi_union_left, measureReal_union (by simp) (measurableSet_singleton x),
    measureReal_def (s := {x}), studentTMeasure_singleton, ENNReal.toReal_zero, add_zero,
    ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- **Exact Student `t` quantile**: for `k ≥ 1` and `u ∈ (0, 1)`, the merged generalized
inverse `cdfQuantile` of `t_k` hits level `u` exactly. -/
theorem cdf_studentTMeasure_cdfQuantile {k : ℕ} (hk : 0 < k) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    cdf (studentTMeasure k) (cdfQuantile (studentTMeasure k) u) = u :=
  cdf_cdfQuantile_of_continuous (continuous_cdf_studentTMeasure hk) hu

/-! ### Snedecor's `F` law: no atoms, continuity, quantiles -/

/-- Snedecor's `F` law has no atoms. -/
theorem snedecorFMeasure_singleton (d₁ d₂ : ℕ) (x : ℝ) : snedecorFMeasure d₁ d₂ {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- **Continuity of the Snedecor `F` cdf**: for `d₁, d₂ ≥ 1` the cdf of `F(d₁, d₂)` is
continuous. -/
theorem continuous_cdf_snedecorFMeasure {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    Continuous (cdf (snedecorFMeasure d₁ d₂)) := by
  have := isProbabilityMeasure_snedecorFMeasure h₁ h₂
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rw [MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero]
  exact snedecorFMeasure_singleton d₁ d₂ x

/-- **Exact Snedecor `F` quantile**: for `d₁, d₂ ≥ 1` and `u ∈ (0, 1)`, the merged generalized
inverse `cdfQuantile` of `F(d₁, d₂)` hits level `u` exactly. -/
theorem cdf_snedecorFMeasure_cdfQuantile {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    cdf (snedecorFMeasure d₁ d₂) (cdfQuantile (snedecorFMeasure d₁ d₂) u) = u :=
  cdf_cdfQuantile_of_continuous (continuous_cdf_snedecorFMeasure h₁ h₂) hu

/-! ### Exact one-sample `t` intervals (variance unknown) -/

/-- The one-sample `t` statistic `√n (X̄ - μ) / S` has law `t_{n-1}` and the sample standard
deviation `S` is almost surely positive. -/
private theorem oneSample_t_facts {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    HasLaw (fun ω => √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)))
        (studentTMeasure (n - 1)) P ∧
      ∀ᵐ ω ∂P, 0 < √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) := by
  have hTmeas : Measurable (fun x : Fin n → ℝ => √(n : ℝ) * ((∑ i, x i) / n - μ) /
      √((∑ i, (x i - (∑ j, x j) / n) ^ 2) / ((n : ℝ) - 1))) := by fun_prop
  have hT : HasLaw (fun ω => √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)))
      (studentTMeasure (n - 1)) P :=
    (⟨hTmeas, map_tStatistic_pi_gaussianReal hn μ hv⟩ : MeasurePreserving _ _ _).fun_comp_hasLaw hX
  refine ⟨hT, ?_⟩
  have h0 : P ((fun ω => √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1))) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hT.aemeasurable (measurableSet_singleton 0),
      hT.map_eq, studentTMeasure_singleton]
  refine measure_mono_null (fun ω (hω : ¬ 0 < _) => ?_) h0
  rw [Set.mem_preimage, Set.mem_singleton_iff,
    le_antisymm (not_lt.mp hω) (Real.sqrt_nonneg _), div_zero]

/-- **Two-sided one-sample `t` interval, exact coverage at every threshold** (variance
unknown). For an i.i.d. `N(μ, v)` sample of size `n ≥ 2` with `v ≠ 0`, write
`X̄ = (∑ Xᵢ) / n` and `S = √(∑ (Xᵢ - X̄)² / (n - 1))`. For every real `c`,
`P(|X̄ - μ| ≤ c S / √n) = t_{n-1}([-c, c])`, with Student's `t` law on `n - 1` degrees of
freedom. -/
theorem one_sample_t_interval_measureReal_eq {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal}
    (hv : v ≠ 0) (c : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    P.real {ω | |(∑ i, X ω i) / n - μ| ≤ c *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} =
      (studentTMeasure (n - 1)).real (Icc (-c) c) := by
  obtain ⟨hT, hS⟩ := oneSample_t_facts hn μ hv hX
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [← ofPred_mem_eq (s := Icc (-c) c),
    ← hT.measureReal_eq (p := fun t => t ∈ Icc (-c) c) measurableSet_Icc]
  refine measureReal_congr (Filter.eventuallyEqSet_iff.mpr ?_)
  filter_upwards [hS] with ω hω
  simp only [mem_Icc, ← abs_le]
  rw [abs_div, abs_mul, abs_of_pos hsn, abs_of_pos hω, div_le_iff₀ hω, le_div_iff₀ hsn,
    mul_comm _ √(n : ℝ)]

/-- **Lower one-sided `t` confidence bound, exact coverage at every threshold** (variance
unknown). Same setting as `one_sample_t_interval_measureReal_eq`: for every real `c`,
`P(X̄ - c S / √n ≤ μ) = F_{t_{n-1}}(c)`. -/
theorem one_sample_t_lower_bound_measureReal_eq {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal}
    (hv : v ≠ 0) (c : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    P.real {ω | (∑ i, X ω i) / n - c *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ) ≤ μ} =
      cdf (studentTMeasure (n - 1)) c := by
  obtain ⟨hT, hS⟩ := oneSample_t_facts hn μ hv hX
  have := isProbabilityMeasure_studentTMeasure (show 0 < n - 1 by omega)
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [cdf_eq_real, ← ofPred_mem_eq (s := Iic c),
    ← hT.measureReal_eq (p := fun t => t ∈ Iic c) measurableSet_Iic]
  refine measureReal_congr (Filter.eventuallyEqSet_iff.mpr ?_)
  filter_upwards [hS] with ω hω
  simp only [mem_Iic]
  rw [div_le_iff₀ hω, sub_le_comm, ← sub_nonneg, ← sub_nonneg (b := √(n : ℝ) * _)]
  constructor <;> intro h
  · have := mul_nonneg h hsn.le
    rw [sub_mul, div_mul_cancel₀ _ hsn.ne'] at this
    linarith
  · have := div_nonneg h hsn.le
    rw [sub_div, mul_div_cancel_left₀ _ hsn.ne'] at this
    linarith

/-- **Upper one-sided `t` confidence bound, exact coverage at every threshold** (variance
unknown). Same setting as `one_sample_t_interval_measureReal_eq`: for every real `c`,
`P(μ ≤ X̄ + c S / √n) = F_{t_{n-1}}(c)`, by symmetry of Student's `t` law. -/
theorem one_sample_t_upper_bound_measureReal_eq {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal}
    (hv : v ≠ 0) (c : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    P.real {ω | μ ≤ (∑ i, X ω i) / n + c *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} =
      cdf (studentTMeasure (n - 1)) c := by
  obtain ⟨hT, hS⟩ := oneSample_t_facts hn μ hv hX
  have := isProbabilityMeasure_studentTMeasure (show 0 < n - 1 by omega)
  have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hsym : cdf (studentTMeasure (n - 1)) c = (studentTMeasure (n - 1)).real (Ici (-c)) := by
    rw [cdf_eq_real, measureReal_def, measureReal_def, ← studentTMeasure_Iic_neg, neg_neg]
  rw [hsym, ← ofPred_mem_eq (s := Ici (-c)),
    ← hT.measureReal_eq (p := fun t => t ∈ Ici (-c)) measurableSet_Ici]
  refine measureReal_congr (Filter.eventuallyEqSet_iff.mpr ?_)
  filter_upwards [hS] with ω hω
  simp only [mem_Ici]
  rw [le_div_iff₀ hω]
  have e : c * √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ) *
      √(n : ℝ) = c * √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) :=
    div_mul_cancel₀ _ hsn.ne'
  constructor <;> intro h <;> nlinarith [e, hsn]

/-- **Exact two-sided one-sample `t` interval at the proved quantile** (variance unknown).
For an i.i.d. `N(μ, v)` sample of size `n ≥ 2` with `v ≠ 0` and `α ∈ (0, 1)`, let
`c = cdfQuantile (t_{n-1}) (1 - α/2)` be the upper `α/2` point of Student's `t` law on `n - 1`
degrees of freedom. Then `P(|X̄ - μ| ≤ c S / √n) = 1 - α` exactly, with
`S = √(∑ (Xᵢ - X̄)² / (n - 1))`. -/
theorem one_sample_t_interval_coverage_eq {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal}
    (hv : v ≠ 0) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    P.real {ω | |(∑ i, X ω i) / n - μ| ≤
      cdfQuantile (studentTMeasure (n - 1)) (1 - α / 2) *
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} = 1 - α := by
  have hk : 0 < n - 1 := by omega
  have := isProbabilityMeasure_studentTMeasure hk
  set c := cdfQuantile (studentTMeasure (n - 1)) (1 - α / 2)
  have hc : cdf (studentTMeasure (n - 1)) c = 1 - α / 2 :=
    cdf_studentTMeasure_cdfQuantile hk ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hcneg : cdf (studentTMeasure (n - 1)) (-c) = α / 2 := by
    rw [cdf_studentTMeasure_neg hk, hc]; ring
  have hc0 : -c ≤ c := by
    by_contra h
    have := monotone_cdf (studentTMeasure (n - 1)) (not_le.mp h).le
    rw [hc, hcneg] at this
    linarith [hα.2]
  rw [one_sample_t_interval_measureReal_eq hn μ hv c hX,
    ← measureReal_congr (Ioc_ae_eq_Icc' (studentTMeasure_singleton _ _)), measureReal_def,
    ← measure_cdf (studentTMeasure (n - 1)), StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_cdf _ hc0)), hc, hcneg]
  ring

/-- **Exact one-sided `t` confidence bounds at the proved quantile** (variance unknown).
For an i.i.d. `N(μ, v)` sample of size `n ≥ 2` with `v ≠ 0` and `α ∈ (0, 1)`, let
`c = cdfQuantile (t_{n-1}) (1 - α)`. Then the lower bound `X̄ - c S / √n ≤ μ` and the upper
bound `μ ≤ X̄ + c S / √n` each hold with probability exactly `1 - α`. -/
theorem one_sample_t_one_sided_coverage_eq {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal}
    (hv : v ≠ 0) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    P.real {ω | (∑ i, X ω i) / n - cdfQuantile (studentTMeasure (n - 1)) (1 - α) *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ) ≤ μ} = 1 - α ∧
    P.real {ω | μ ≤ (∑ i, X ω i) / n + cdfQuantile (studentTMeasure (n - 1)) (1 - α) *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} = 1 - α := by
  have hc := cdf_studentTMeasure_cdfQuantile (show 0 < n - 1 by omega)
    (u := 1 - α) ⟨by linarith [hα.2], by linarith [hα.1]⟩
  exact ⟨(one_sample_t_lower_bound_measureReal_eq hn μ hv _ hX).trans hc,
    (one_sample_t_upper_bound_measureReal_eq hn μ hv _ hX).trans hc⟩

end ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

open Matrix MeasureTheory ProbabilityTheory Set

/-- **Upper tail of the linear-hypothesis `F` statistic at every threshold.** In
`y = X β + ε` with full-rank `X`, `σ > 0`, `σ⁻¹ ε` i.i.d. standard normal, a full-row-rank
hypothesis matrix `C` with `q = card r ≥ 1` rows, `p = card k < n = card m`, and under
`H₀ : C β = γ`, the rejection probability of `F > c` is `1 - F_{F(q, n - p)}(c)` for every real
`c`, with Snedecor's `F` law on `(q, n - p)` degrees of freedom. -/
theorem fStatistic_measureReal_gt_eq {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) (hr : 0 < Fintype.card r)
    (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {γ : r → ℝ} (hβ : C *ᵥ β = γ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) (c : ℝ) :
    μ.real {ω | c < fStatistic X C γ (X *ᵥ β + ε ω)} =
      1 - cdf (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)) c := by
  have := isProbabilityMeasure_snedecorFMeasure hr (Nat.sub_pos_of_lt hkm)
  rw [(hasLaw_fStatistic hX hC hr hkm β hβ hσ hε).measureReal_eq (p := fun x => c < x)
      measurableSet_Ioi, cdf_eq_real]
  change (snedecorFMeasure _ _).real (Ioi c) = _
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- **Exact-size `F` test at the proved quantile.** Same setting as
`fStatistic_measureReal_gt_eq`. For `α ∈ (0, 1)`, the test rejecting `H₀ : C β = γ` when
`F > cdfQuantile (F(q, n - p)) (1 - α)` has size exactly `α`. -/
theorem fTest_size_eq {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) (hr : 0 < Fintype.card r)
    (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {γ : r → ℝ} (hβ : C *ᵥ β = γ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    μ.real {ω | cdfQuantile (snedecorFMeasure (Fintype.card r)
        (Fintype.card m - Fintype.card k)) (1 - α) < fStatistic X C γ (X *ᵥ β + ε ω)} = α := by
  rw [fStatistic_measureReal_gt_eq hX hC hr hkm β hβ hσ hε,
    cdf_snedecorFMeasure_cdfQuantile hr (Nat.sub_pos_of_lt hkm)
      ⟨by linarith [hα.2], by linarith [hα.1]⟩]
  ring

/-- **Exact `F` confidence region for `C β`.** In `y = X β + ε` with full-rank `X`, `σ > 0`,
`σ⁻¹ ε` i.i.d. standard normal, a full-row-rank `C` with `q = card r ≥ 1`, `p < n`, and
`α ∈ (0, 1)`, the region `{γ | F(γ; y) ≤ cdfQuantile (F(q, n - p)) (1 - α)}` (an ellipsoid
centred at `C β̂`) contains the true `C β` with probability exactly `1 - α`, for every `β`. -/
theorem fConfidenceRegion_coverage_eq {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) (hr : 0 < Fintype.card r)
    (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    μ.real {ω | C *ᵥ β ∈ {γ : r → ℝ | fStatistic X C γ (X *ᵥ β + ε ω) ≤
        cdfQuantile (snedecorFMeasure (Fintype.card r)
          (Fintype.card m - Fintype.card k)) (1 - α)}} = 1 - α := by
  have := isProbabilityMeasure_snedecorFMeasure hr (Nat.sub_pos_of_lt hkm)
  have hP : IsProbabilityMeasure μ := hε.isProbabilityMeasure
  have hsize := fTest_size_eq hX hC hr hkm β rfl hσ hε hα
  have hcompl : {ω | C *ᵥ β ∈ {γ : r → ℝ | fStatistic X C γ (X *ᵥ β + ε ω) ≤
        cdfQuantile (snedecorFMeasure (Fintype.card r)
          (Fintype.card m - Fintype.card k)) (1 - α)}} =
      {ω | cdfQuantile (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k))
        (1 - α) < fStatistic X C (C *ᵥ β) (X *ᵥ β + ε ω)}ᶜ := by
    ext ω; simp
  have hF := hasLaw_fStatistic hX hC hr hkm β (rfl : C *ᵥ β = C *ᵥ β) hσ hε
  have hmeas : NullMeasurableSet {ω | cdfQuantile (snedecorFMeasure (Fintype.card r)
      (Fintype.card m - Fintype.card k)) (1 - α) < fStatistic X C (C *ᵥ β) (X *ᵥ β + ε ω)} μ :=
    hF.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi
  rw [hcompl, probReal_compl_eq_one_sub₀ hmeas, hsize]

end MathlibExt.Probability.Statistics.LinearModel

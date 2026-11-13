/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.StudentT
public import MathlibExt.Probability.Distributions.SnedecorF
public import MathlibExt.Probability.Quantile
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.FiniteProbability
import MathlibExt.Probability.Statistics.LinearModel.Inference
import MathlibExt.Probability.Statistics.Slutsky
import MathlibExt.Probability.CdfContinuityPoints

/-!
# Exact two-sample normal theory: pooled `t` and variance-ratio `F`

Two independent i.i.d. normal samples `X₁, …, X_m ~ N(μ₁, v₁)` and `Y₁, …, Y_n ~ N(μ₂, v₂)`.
Write `X̄ = (∑ Xᵢ) / m`, `Ȳ = (∑ Yⱼ) / n`.

**Pooled `t`** (common variance `v₁ = v₂ = v > 0`, `m, n ≥ 1`, `m + n ≥ 3`). With
`S_p² = (∑ (Xᵢ - X̄)² + ∑ (Yⱼ - Ȳ)²) / (m + n - 2)` (`pooledVariance`), the statistic
`T = (X̄ - Ȳ - (μ₁ - μ₂)) / (S_p √(1/m + 1/n))` (`twoSampleTStatistic`) has Student's `t` law
with `m + n - 2` degrees of freedom. The proof is the contrast `t` law
`MathlibExt.Probability.Statistics.LinearModel.hasLaw_tStatistic` for the two-group design
(one indicator column per sample) and the contrast `(1, -1)`: the OLS estimator is `(X̄, Ȳ)`,
the contrast variance is `1/m + 1/n`, and the residual sum of squares is the pooled sum of
squares. Independence of the samples turns the two product laws into the i.i.d. normal law
on `Fin m ⊕ Fin n` (`measurePreserving_sumPiEquivProdPi_symm`).

**Variance-ratio `F`** (`m, n ≥ 2`, `v₁, v₂ > 0`). With unbiased sample variances `S_X²`, `S_Y²`
and `R = S_X² / S_Y²` (`varianceRatio`), `R / (v₁ / v₂) ~ F(m - 1, n - 1)`: each
`∑ (Xᵢ - X̄)² / v₁` is `χ²_{m-1}` (the intercept-only residual sum of squares,
`hasLaw_rss_div_sq`), the two are independent, and the merged ratio law
`map_div_chiSquare_eq_snedecorF` applies.

**Quantiles.** Both laws have Lebesgue densities, hence no atoms and continuous cdfs, so the
merged generalized inverse `cdfQuantile` hits every level in `(0, 1)` exactly; the `t` cdf is
symmetric. These facts are proved here as private lemmas, because the public versions live in
`NormalTheory.lean` (open PR #1566), which this file does not import. With them, coverage and
size statements are equalities, not inequalities.

**Slutsky.** Without normality, if the known-variance statistic converges in distribution and
`S_p² → σ²` in probability, the pooled `t` statistic has the same limit (inputs taken as
hypotheses; no central limit theorem or law of large numbers is proved here).

## Main results

* `hasLaw_twoSampleTStatistic`: `T ~ t_{m+n-2}`.
* `twoSample_t_interval_measureReal_eq`: for every real `c`,
  `P(|X̄ - Ȳ - (μ₁ - μ₂)| ≤ c S_p √(1/m + 1/n)) = t_{m+n-2}([-c, c])`.
* `twoSample_t_interval_coverage_eq`: with `c = q_{t_{m+n-2}}(1 - α/2)`, coverage is exactly
  `1 - α`.
* `twoSample_t_test_size_eq`, `twoSample_t_one_sided_test_size_eq`: the two-sided and one-sided
  pooled `t` tests have size exactly `α`.
* `pooledVariance_eq_sampleMean`, `varianceRatio_eq`: bridges to the canonical `sampleMean` and
  `sampleVarUnbiased` of `MathlibExt.Probability.FiniteProbability`.
* `hasLaw_varianceRatio_div`: `(S_X² / S_Y²) / (v₁ / v₂) ~ F(m - 1, n - 1)`;
  `hasLaw_varianceRatio`: `S_X² / S_Y² ~ F(m - 1, n - 1)` when `v₁ = v₂`.
* `varianceRatio_test_size_eq`: the one-sided `F` test of `v₁ = v₂` has size exactly `α`.
* `varianceRatio_interval_coverage_eq`: `[R / q(1 - α/2), R / q(α/2)]` covers `v₁ / v₂` with
  probability exactly `1 - α`.
* `tendstoInDistribution_twoSampleTStatistic`: Slutsky transfer of a limit law to `T`.

Not covered: Welch's statistic for unequal variances, power under alternatives.

## References

* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §5.3 (comparing the means and the variances of two normal distributions: the pooled
  two-sample `t` test and the variance-ratio `F` test).
* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002),
  Theorem 5.3.1 (`(n - 1) S² / σ² ~ χ²_{n-1}`), Definitions 5.3.4 and 5.3.6 (`t` and `F` laws).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), Lemma 2.8 (Slutsky).
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Real Matrix MathlibExt.Probability.Statistics.LinearModel

/-! ### The two-sample statistics -/

/-- The **pooled sample variance** of two samples `x : Fin m → ℝ`, `y : Fin n → ℝ`:
`S_p² = (∑ᵢ (xᵢ - x̄)² + ∑ⱼ (yⱼ - ȳ)²) / (m + n - 2)` with `x̄ = (∑ᵢ xᵢ) / m`,
`ȳ = (∑ⱼ yⱼ) / n` (Lehmann–Romano, §5.3). Meant for `m + n ≥ 3`. -/
noncomputable def pooledVariance {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - (∑ i', x i') / m) ^ 2 + ∑ j, (y j - (∑ j', y j') / n) ^ 2) /
    ((m : ℝ) + n - 2)

/-- The **pooled two-sample `t` statistic** for the mean difference `δ`:
`T = (x̄ - ȳ - δ) / (S_p √(1/m + 1/n))`, with `S_p² = pooledVariance x y`. -/
noncomputable def twoSampleTStatistic {m n : ℕ} (δ : ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  ((∑ i, x i) / m - (∑ j, y j) / n - δ) / √(pooledVariance x y * (1 / m + 1 / n))

/-! ### The two-group design -/

/-- The two-group (one-way, two-level) design: an observation in the first sample loads on the
first coefficient, one in the second sample on the second. -/
private def twoGroupDesign (m n : ℕ) : Matrix (Fin m ⊕ Fin n) (Fin 2) ℝ :=
  Matrix.of (Sum.elim (fun _ => ![1, 0]) (fun _ => ![0, 1]))

private lemma twoGroupDesign_mulVec (m n : ℕ) (b : Fin 2 → ℝ) :
    twoGroupDesign m n *ᵥ b = Sum.elim (fun _ => b 0) (fun _ => b 1) := by
  ext (i | i) <;> simp [twoGroupDesign, mulVec, dotProduct, Fin.sum_univ_two]

private lemma twoGroupDesign_gram (m n : ℕ) :
    (twoGroupDesign m n)ᵀ * twoGroupDesign m n = !![(m : ℝ), 0; 0, (n : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoGroupDesign, Matrix.mul_apply, Fintype.sum_sum_type]

private lemma twoGroupDesign_isUnit_gram {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    IsUnit ((twoGroupDesign m n)ᵀ * twoGroupDesign m n) := by
  rw [Matrix.isUnit_iff_isUnit_det, twoGroupDesign_gram, Matrix.det_fin_two_of]
  simpa using And.intro hm hn

private lemma twoGroupDesign_gram_inv {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ((twoGroupDesign m n)ᵀ * twoGroupDesign m n)⁻¹ = !![(m : ℝ)⁻¹, 0; 0, (n : ℝ)⁻¹] := by
  rw [twoGroupDesign_gram]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hm, hn]

private lemma olsEstimator_twoGroupDesign {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (z : Fin m ⊕ Fin n → ℝ) :
    olsEstimator (twoGroupDesign m n) z =
      ![(∑ i, z (Sum.inl i)) / m, (∑ j, z (Sum.inr j)) / n] := by
  rw [olsEstimator, olsMatrix_eq, twoGroupDesign_gram_inv hm hn]
  ext j
  fin_cases j <;>
    simp [twoGroupDesign, mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Finset.mul_sum, div_eq_inv_mul]

private lemma contrastVariance_twoGroupDesign {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    contrastVariance (twoGroupDesign m n) ![1, -1] = 1 / m + 1 / n := by
  rw [contrastVariance, twoGroupDesign_gram_inv hm hn]
  simp [mulVec, dotProduct, Fin.sum_univ_two]

private lemma tStatistic_twoGroupDesign {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 2 ≤ m + n)
    (μ₁ μ₂ : ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    tStatistic (twoGroupDesign m n) ![1, -1] ![μ₁, μ₂] (Sum.elim x y) =
      twoSampleTStatistic (μ₁ - μ₂) x y := by
  have hnum : ![(1 : ℝ), -1] ⬝ᵥ (![(∑ i, x i) / m, (∑ j, y j) / n] - ![μ₁, μ₂]) =
      (∑ i, x i) / m - (∑ j, y j) / n - (μ₁ - μ₂) := by
    simp [dotProduct, Fin.sum_univ_two]
    ring
  have hrss : (Sum.elim x y - Sum.elim (fun _ => (∑ i, x i) / m) fun _ => (∑ j, y j) / n) ⬝ᵥ
      (Sum.elim x y - Sum.elim (fun _ => (∑ i, x i) / m) fun _ => (∑ j, y j) / n) =
      ∑ i, (x i - (∑ i', x i') / m) ^ 2 + ∑ j, (y j - (∑ j', y j') / n) ^ 2 := by
    simp [dotProduct, Fintype.sum_sum_type, sq]
  have hcast : ((Fintype.card (Fin m ⊕ Fin n) - Fintype.card (Fin 2) : ℕ) : ℝ) =
      (m : ℝ) + n - 2 := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, Nat.cast_sub hmn]
    push_cast
    ring
  rw [tStatistic, olsEstimator_twoGroupDesign hm hn, twoGroupDesign_mulVec,
    contrastVariance_twoGroupDesign hm hn, hcast]
  simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [hnum, hrss]
  rfl

/-- Standardizing an i.i.d. `N(μ, v)` sample coordinatewise gives an i.i.d. standard normal
sample (same argument as the private helper of `LinearModel.Inference`). -/
private lemma hasLaw_pi_gaussianReal_standardize' {n : ℕ} (μ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    HasLaw (fun x : Fin n → ℝ => (√(v : ℝ))⁻¹ • (x - fun _ => μ))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (Measure.pi fun _ : Fin n => gaussianReal μ v) := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hcoord : (gaussianReal μ v).map (fun y => (√(v : ℝ))⁻¹ * (y - μ)) =
      gaussianReal 0 1 := by
    rw [show (fun y => (√(v : ℝ))⁻¹ * (y - μ)) = (fun y => (√(v : ℝ))⁻¹ * y) ∘ (fun y => y - μ)
        from rfl, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
      gaussianReal_map_const_mul, sub_self, mul_zero]
    congr 1
    ext
    simp [inv_pow, Real.sq_sqrt hv0.le, hv0.ne']
  refine ⟨by fun_prop, ?_⟩
  change (Measure.pi fun _ : Fin n => gaussianReal μ v).map
    (fun x i => (√(v : ℝ))⁻¹ * (x i - μ)) = _
  rw [Measure.pi_map_pi (f := fun _ y => (√(v : ℝ))⁻¹ * (y - μ))
    (hμ := fun _ => by rw [hcoord]; infer_instance) (fun _ => by fun_prop)]
  simp only [hcoord]

/-- The standardized noise of the two-group model is i.i.d. standard normal: for independent
samples `X ~ N(μ₁, v)^m`, `Y ~ N(μ₂, v)^n`, `v^{-1/2} (Sum.elim X Y - D (μ₁, μ₂))` has law
`N(0, 1)^{m+n}`. -/
private lemma hasLaw_twoGroup_noise {m n : ℕ} (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v) P) (hXY : IndepFun X Y P) :
    HasLaw (fun ω => (√(v : ℝ))⁻¹ •
        (Sum.elim (X ω) (Y ω) - twoGroupDesign m n *ᵥ ![μ₁, μ₂]))
      (Measure.pi fun _ : Fin m ⊕ Fin n => gaussianReal 0 1) P := by
  have := hX.isProbabilityMeasure
  have hpair := (indepFun_iff_hasLaw_prodMk_prod hX hY).1 hXY
  have hstd := ((hasLaw_pi_gaussianReal_standardize' (n := m) μ₁ hv).measurePreserving
      (by fun_prop)).prod
    ((hasLaw_pi_gaussianReal_standardize' (n := n) μ₂ hv).measurePreserving (by fun_prop))
  have hsum := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin m ⊕ Fin n => gaussianReal 0 1)
  have h := (hsum.comp hstd).comp_hasLaw hpair
  refine h.congr (ae_of_all _ fun ω => ?_)
  ext (i | i) <;>
    simp [twoGroupDesign_mulVec, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.sumPiEquivProdPi]

/-! ### The exact two-sample `t` law -/

/-- **Two-sample `t` law with pooled variance** (Lehmann–Romano, §5.3). Let
`X₁, …, X_m ~ N(μ₁, v)` and `Y₁, …, Y_n ~ N(μ₂, v)` be independent i.i.d. samples with
a common variance `v > 0`, `m, n ≥ 1` and `m + n ≥ 3`. Then
`(X̄ - Ȳ - (μ₁ - μ₂)) / (S_p √(1/m + 1/n))` has Student's `t` law with `m + n - 2` degrees of
freedom, where `S_p² = (∑ (Xᵢ - X̄)² + ∑ (Yⱼ - Ȳ)²) / (m + n - 2)`. -/
theorem hasLaw_twoSampleTStatistic {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : 3 ≤ m + n)
    (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v) P) (hXY : IndepFun X Y P) :
    HasLaw (fun ω => twoSampleTStatistic (μ₁ - μ₂) (X ω) (Y ω))
      (studentTMeasure (m + n - 2)) P := by
  have hσ : 0 < √(v : ℝ) := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
  have h := hasLaw_tStatistic (twoGroupDesign_isUnit_gram (m := m) (n := n) (by omega)
      (by omega))
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]; omega)
    ![μ₁, μ₂] hσ (hasLaw_twoGroup_noise μ₁ μ₂ hv hX hY hXY) (a := ![1, -1])
    (fun h => one_ne_zero (congrFun h 0))
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at h
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only
  rw [add_sub_cancel, tStatistic_twoGroupDesign (by omega) (by omega) (by omega)]

/-! ### Quantile facts for the `t` and `F` laws

TODO(#1566): after `NormalTheory.lean` (open PR #1566, not imported here) merges, replace the
private copies `studentTMeasure_singleton'`, `studentTMeasure_Iic_neg'`,
`cdf_studentTMeasure_neg'` and `snedecorFMeasure_singleton'` by its public
`studentTMeasure_singleton`, `studentTMeasure_Iic_neg`, `cdf_studentTMeasure_neg` and
`snedecorFMeasure_singleton`, and the uses of `cdf_cdfQuantile_of_noAtom` by
`cdf_studentTMeasure_cdfQuantile` / `cdf_snedecorFMeasure_cdfQuantile`.
`cdf_cdfQuantile_of_noAtom` itself, `measureReal_Icc_of_noAtom`, `studentT_central_mass` and
`snedecorFMeasure_Iic_zero` have no public counterpart there and stay. -/

/-- A law without atoms has a continuous cdf, so the generalized inverse is exact on `(0, 1)`. -/
private lemma cdf_cdfQuantile_of_noAtom {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h0 : ∀ x, ν {x} = 0) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    cdf ν (cdfQuantile ν u) = u := by
  have hν : Continuous (cdf ν) := continuous_iff_continuousAt.mpr fun x =>
    (MathlibExt.Probability.CdfContinuityPoints.continuousAt_cdf_iff_measure_singleton_eq_zero
      ν x).mpr (h0 x)
  refine le_antisymm ?_ (cdfQuantile_mem ν hu)
  set q := cdfQuantile ν u
  have hlt : ∀ x < q, cdf ν x ≤ u := fun x hx => by
    by_contra h
    exact (not_le.mpr hx) ((cdfQuantile_le_iff ν hu).mpr (not_le.mp h).le)
  have ht : Filter.Tendsto (cdf ν) (nhdsWithin q (Set.Iio q)) (nhds (cdf ν q)) :=
    hν.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with x hx using hlt x hx)

/-- For a law without atoms, the mass of `[a, b]` is the cdf increment. -/
private lemma measureReal_Icc_of_noAtom {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h0 : ∀ x, ν {x} = 0) {a b : ℝ} (hab : a ≤ b) :
    ν.real (Set.Icc a b) = cdf ν b - cdf ν a := by
  have : NullSingletonClass ν := ⟨h0⟩
  rw [measureReal_def, ← measure_congr Ioc_ae_eq_Icc,
    MathlibExt.Probability.CdfContinuityPoints.measure_Ioc_eq_ofReal_cdf,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_cdf ν hab))]

private lemma studentTMeasure_singleton' (k : ℕ) (x : ℝ) : studentTMeasure k {x} = 0 :=
  withDensity_absolutelyContinuous _ _ Real.volume_singleton

private lemma studentTMeasure_Iic_neg' (k : ℕ) (x : ℝ) :
    studentTMeasure k (Set.Iic (-x)) = studentTMeasure k (Set.Ici x) := by
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal
    (Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) *
      (1 + t ^ 2 / k) ^ (-((k : ℝ) + 1) / 2)) with hf
  have hfm : Measurable f := by fun_prop
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Iic (-x) = Set.Ici x := by
    ext t; simp
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
    (measurableSet_Iic (a := -x)) hfm
  rw [hpre] at h
  have heven : (fun t => f (-t)) = f := by funext t; simp [hf]
  rw [heven] at h
  rw [studentTMeasure, withDensity_apply _ measurableSet_Iic,
    withDensity_apply _ measurableSet_Ici, ← hf, h]

/-- Symmetry of the `t` cdf: `F(-x) = 1 - F(x)`. -/
private lemma cdf_studentTMeasure_neg' {k : ℕ} (hk : 0 < k) (x : ℝ) :
    cdf (studentTMeasure k) (-x) = 1 - cdf (studentTMeasure k) x := by
  have := isProbabilityMeasure_studentTMeasure hk
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, studentTMeasure_Iic_neg', ← measureReal_def,
    ← Set.Ioi_union_left, measureReal_union (by simp) (measurableSet_singleton x),
    measureReal_def (s := {x}), studentTMeasure_singleton', ENNReal.toReal_zero, add_zero,
    ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- The two-sided `t` critical value: `c = q_{t_k}(1 - α/2)` is positive and
`t_k([-c, c]) = 1 - α`. -/
private lemma studentT_central_mass {k : ℕ} (hk : 0 < k) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    0 < cdfQuantile (studentTMeasure k) (1 - α / 2) ∧
      (studentTMeasure k).real (Set.Icc (-cdfQuantile (studentTMeasure k) (1 - α / 2))
        (cdfQuantile (studentTMeasure k) (1 - α / 2))) = 1 - α := by
  have := isProbabilityMeasure_studentTMeasure hk
  have hu : 1 - α / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hq := cdf_cdfQuantile_of_noAtom (studentTMeasure_singleton' k) hu
  have h0 : cdf (studentTMeasure k) 0 = 1 / 2 := by
    have := cdf_studentTMeasure_neg' hk 0
    rw [neg_zero] at this
    linarith
  have hpos : 0 < cdfQuantile (studentTMeasure k) (1 - α / 2) := by
    by_contra h
    have := (cdfQuantile_le_iff _ hu).mp (not_lt.mp h)
    linarith [hα.2]
  refine ⟨hpos, ?_⟩
  rw [measureReal_Icc_of_noAtom (studentTMeasure_singleton' k) (by linarith),
    cdf_studentTMeasure_neg' hk, hq]
  ring

/-! ### Exact two-sample `t` intervals and tests -/

/-- The pooled two-sample `t` statistic has law `t_{m+n-2}` and its denominator is almost
surely positive. -/
private lemma twoSample_t_facts {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : 3 ≤ m + n)
    (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v) P) (hXY : IndepFun X Y P) :
    HasLaw (fun ω => twoSampleTStatistic (μ₁ - μ₂) (X ω) (Y ω))
        (studentTMeasure (m + n - 2)) P ∧
      ∀ᵐ ω ∂P, 0 < √(pooledVariance (X ω) (Y ω) * (1 / m + 1 / n)) := by
  have hT := hasLaw_twoSampleTStatistic hm hn hmn μ₁ μ₂ hv hX hY hXY
  refine ⟨hT, ?_⟩
  have h0 : P ((fun ω => twoSampleTStatistic (μ₁ - μ₂) (X ω) (Y ω)) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hT.aemeasurable (measurableSet_singleton 0),
      hT.map_eq, studentTMeasure_singleton']
  refine measure_mono_null (fun ω (hω : ¬ 0 < _) => ?_) h0
  rw [Set.mem_preimage, Set.mem_singleton_iff, twoSampleTStatistic,
    le_antisymm (not_lt.mp hω) (Real.sqrt_nonneg _), div_zero]

/-- **Two-sample `t` interval, exact coverage at every threshold.** For independent samples
`X ~ N(μ₁, v)^m`, `Y ~ N(μ₂, v)^n` with `v > 0`, `m, n ≥ 1`, `m + n ≥ 3`, and every real `c`,
`P(|X̄ - Ȳ - (μ₁ - μ₂)| ≤ c S_p √(1/m + 1/n)) = t_{m+n-2}([-c, c])`. -/
theorem twoSample_t_interval_measureReal_eq {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 3 ≤ m + n) (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0) (c : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v) P) (hXY : IndepFun X Y P) :
    P.real {ω | |(∑ i, X ω i) / m - (∑ j, Y ω j) / n - (μ₁ - μ₂)| ≤
        c * √(pooledVariance (X ω) (Y ω) * (1 / m + 1 / n))} =
      (studentTMeasure (m + n - 2)).real (Set.Icc (-c) c) := by
  obtain ⟨hT, hS⟩ := twoSample_t_facts hm hn hmn μ₁ μ₂ hv hX hY hXY
  rw [← Set.ofPred_mem_eq (s := Set.Icc (-c) c),
    ← hT.measureReal_eq (p := fun t => t ∈ Set.Icc (-c) c) measurableSet_Icc]
  refine measureReal_congr (Filter.eventuallyEqSet_iff.mpr ?_)
  filter_upwards [hS] with ω hω
  simp only [Set.mem_Icc, ← abs_le, twoSampleTStatistic]
  rw [abs_div, abs_of_pos hω, div_le_iff₀ hω]

/-- **Two-sample `t` interval with exact coverage `1 - α`.** With the critical value
`c = q_{t_{m+n-2}}(1 - α/2)` (the `cdfQuantile` of Student's `t` law), the interval
`X̄ - Ȳ ± c S_p √(1/m + 1/n)` covers `μ₁ - μ₂` with probability exactly `1 - α`. -/
theorem twoSample_t_interval_coverage_eq {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 3 ≤ m + n) (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v) P) (hXY : IndepFun X Y P) :
    P.real {ω | |(∑ i, X ω i) / m - (∑ j, Y ω j) / n - (μ₁ - μ₂)| ≤
        cdfQuantile (studentTMeasure (m + n - 2)) (1 - α / 2) *
          √(pooledVariance (X ω) (Y ω) * (1 / m + 1 / n))} = 1 - α := by
  rw [twoSample_t_interval_measureReal_eq hm hn hmn μ₁ μ₂ hv _ hX hY hXY]
  exact (studentT_central_mass (by omega) hα).2

/-- **Exact size of the two-sided pooled `t` test.** Under `H₀ : μ₁ - μ₂ = δ`, rejecting when
`|T| > q_{t_{m+n-2}}(1 - α/2)` has probability exactly `α`. -/
theorem twoSample_t_test_size_eq {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 3 ≤ m + n) (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v) P) (hXY : IndepFun X Y P) :
    P.real {ω | cdfQuantile (studentTMeasure (m + n - 2)) (1 - α / 2) <
        |twoSampleTStatistic (μ₁ - μ₂) (X ω) (Y ω)|} = α := by
  have := isProbabilityMeasure_studentTMeasure (k := m + n - 2) (by omega)
  have hT := hasLaw_twoSampleTStatistic hm hn hmn μ₁ μ₂ hv hX hY hXY
  set c := cdfQuantile (studentTMeasure (m + n - 2)) (1 - α / 2)
  have hset : {t : ℝ | c < |t|} = (Set.Icc (-c) c)ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
  rw [hT.measureReal_eq (p := fun t => c < |t|) (measurableSet_lt measurable_const
    (by fun_prop)), hset, probReal_compl_eq_one_sub measurableSet_Icc,
    (studentT_central_mass (by omega) hα).2]
  ring

/-- **Exact size of the one-sided pooled `t` test.** Under `H₀ : μ₁ - μ₂ = δ`, rejecting when
`T > q_{t_{m+n-2}}(1 - α)` has probability exactly `α`. -/
theorem twoSample_t_one_sided_test_size_eq {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 3 ≤ m + n) (μ₁ μ₂ : ℝ) {v : NNReal} (hv : v ≠ 0) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v) P) (hXY : IndepFun X Y P) :
    P.real {ω | cdfQuantile (studentTMeasure (m + n - 2)) (1 - α) <
        twoSampleTStatistic (μ₁ - μ₂) (X ω) (Y ω)} = α := by
  have := isProbabilityMeasure_studentTMeasure (k := m + n - 2) (by omega)
  have hT := hasLaw_twoSampleTStatistic hm hn hmn μ₁ μ₂ hv hX hY hXY
  have hu : 1 - α ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have h := hT.measureReal_eq
    (p := fun t => t ∈ Set.Ioi (cdfQuantile (studentTMeasure (m + n - 2)) (1 - α)))
    measurableSet_Ioi
  rw [Set.ofPred_mem_eq] at h
  refine h.trans ?_
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_cdfQuantile_of_noAtom (studentTMeasure_singleton' _) hu]
  ring

/-! ### The variance-ratio `F` test -/

/-- The **variance ratio** `S_X² / S_Y²` of two samples, with the unbiased sample variances
`S_X² = ∑ᵢ (xᵢ - x̄)² / (m - 1)` and `S_Y² = ∑ⱼ (yⱼ - ȳ)² / (n - 1)` (Lehmann–Romano,
§5.3). Meant for `m, n ≥ 2`. -/
noncomputable def varianceRatio {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  ((∑ i, (x i - (∑ i', x i') / m) ^ 2) / ((m : ℝ) - 1)) /
    ((∑ j, (y j - (∑ j', y j') / n) ^ 2) / ((n : ℝ) - 1))

open MathlibExt.Probability.FiniteProbability in
/-- `pooledVariance` in terms of the canonical sample mean `sampleMean`. -/
theorem pooledVariance_eq_sampleMean {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    pooledVariance x y =
      (∑ i, (x i - sampleMean x) ^ 2 + ∑ j, (y j - sampleMean y) ^ 2) / ((m : ℝ) + n - 2) := by
  rw [pooledVariance, sampleMean_eq_sum_div, sampleMean_eq_sum_div, Fintype.card_fin,
    Fintype.card_fin]

open MathlibExt.Probability.FiniteProbability in
/-- `varianceRatio` is the ratio of the canonical unbiased sample variances
`sampleVarUnbiased`. -/
theorem varianceRatio_eq {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    varianceRatio x y = sampleVarUnbiased x / sampleVarUnbiased y := by
  rw [varianceRatio, sampleVarUnbiased_eq_sum_div, sampleVarUnbiased_eq_sum_div,
    sampleMean_eq_sum_div, sampleMean_eq_sum_div, Fintype.card_fin, Fintype.card_fin]

/-- The intercept-only design (private helpers as in `LinearModel.Inference`). -/
private def interceptDesign (n : ℕ) : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun _ _ => 1

private lemma interceptDesign_mulVec (n : ℕ) (b : Fin 1 → ℝ) :
    interceptDesign n *ᵥ b = fun _ => b 0 := by
  ext i
  simp [interceptDesign, mulVec, dotProduct]

private lemma interceptDesign_gram_inv {n : ℕ} (hn : n ≠ 0) :
    ((interceptDesign n)ᵀ * interceptDesign n)⁻¹ = Matrix.of fun _ _ => (n : ℝ)⁻¹ := by
  have hg : (interceptDesign n)ᵀ * interceptDesign n = Matrix.of fun _ _ => (n : ℝ) := by
    ext i j
    simp [interceptDesign, Matrix.mul_apply]
  rw [hg]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  simp [Matrix.mul_apply, hn]

private lemma interceptDesign_isUnit_gram {n : ℕ} (hn : n ≠ 0) :
    IsUnit ((interceptDesign n)ᵀ * interceptDesign n) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
  simp [interceptDesign, Matrix.mul_apply, hn]

private lemma olsEstimator_interceptDesign {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℝ) :
    olsEstimator (interceptDesign n) x = fun _ => (∑ i, x i) / n := by
  rw [olsEstimator, olsMatrix_eq, interceptDesign_gram_inv hn]
  ext j
  simp [interceptDesign, mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum, div_eq_inv_mul]

/-- **Sample variance law** (Casella–Berger, Theorem 5.3.1(c)): for an i.i.d. `N(μ, v)` sample of
size `m ≥ 2` with `v > 0`, `∑ (Xᵢ - X̄)² / v ~ χ²_{m-1}`; the residual sum of squares of the
intercept-only model. -/
private lemma hasLaw_sumSq_div_var {m : ℕ} (hm : 2 ≤ m) (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ v) P) :
    HasLaw (fun ω => (∑ i, (X ω i - (∑ j, X ω j) / m) ^ 2) / v)
      (chiSquareMeasure (m - 1)) P := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hσ : 0 < √(v : ℝ) := Real.sqrt_pos.mpr hv0
  have h := hasLaw_rss_div_sq (interceptDesign_isUnit_gram (n := m) (by omega))
    (by rw [Fintype.card_fin, Fintype.card_fin]; omega) (fun _ => μ) (√(v : ℝ)) hσ
    ((hasLaw_pi_gaussianReal_standardize' μ hv).fun_comp hX)
  rw [Fintype.card_fin, Fintype.card_fin] at h
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only
  rw [interceptDesign_mulVec, add_sub_cancel, olsEstimator_interceptDesign (by omega),
    interceptDesign_mulVec, Real.sq_sqrt hv0.le]
  simp [dotProduct, sq]

/-- **Variance-ratio pivot** (Lehmann–Romano, §5.3). For independent samples
`X ~ N(μ₁, v₁)^m`, `Y ~ N(μ₂, v₂)^n` with `v₁, v₂ > 0` and `m, n ≥ 2`,
`(S_X² / S_Y²) / (v₁ / v₂) = (S_X² / v₁) / (S_Y² / v₂)` has Snedecor's `F` law with
`(m - 1, n - 1)` degrees of freedom. -/
theorem hasLaw_varianceRatio_div {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (μ₁ μ₂ : ℝ)
    {v₁ v₂ : NNReal} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v₁) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v₂) P) (hXY : IndepFun X Y P) :
    HasLaw (fun ω => varianceRatio (X ω) (Y ω) / ((v₁ : ℝ) / v₂))
      (snedecorFMeasure (m - 1) (n - 1)) P := by
  have := hX.isProbabilityMeasure
  have hV₁ := hasLaw_sumSq_div_var hm μ₁ hv₁ hX
  have hV₂ := hasLaw_sumSq_div_var hn μ₂ hv₂ hY
  have hV : IndepFun (fun ω => (∑ i, (X ω i - (∑ j, X ω j) / m) ^ 2) / v₁)
      (fun ω => (∑ i, (Y ω i - (∑ j, Y ω j) / n) ^ 2) / v₂) P :=
    hXY.comp (φ := fun x : Fin m → ℝ => (∑ i, (x i - (∑ j, x j) / m) ^ 2) / v₁)
      (ψ := fun y : Fin n → ℝ => (∑ i, (y i - (∑ j, y j) / n) ^ 2) / v₂)
      (by fun_prop) (by fun_prop)
  have hmap := map_div_chiSquare_eq_snedecorF (by omega) (by omega) hV₁ hV₂ hV
  have hfun : (fun ω => varianceRatio (X ω) (Y ω) / ((v₁ : ℝ) / v₂)) =
      fun ω => ((∑ i, (X ω i - (∑ j, X ω j) / m) ^ 2) / v₁ / ((m - 1 : ℕ) : ℝ)) /
        ((∑ i, (Y ω i - (∑ j, Y ω j) / n) ^ 2) / v₂ / ((n - 1 : ℕ) : ℝ)) := by
    funext ω
    rw [varianceRatio, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [hfun]
  exact ⟨(hV₁.aemeasurable.div_const _).div (hV₂.aemeasurable.div_const _), hmap⟩

/-- **Variance-ratio law under equal variances**: if `v₁ = v₂ = v`, then
`S_X² / S_Y² ~ F(m - 1, n - 1)`. -/
theorem hasLaw_varianceRatio {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (μ₁ μ₂ : ℝ)
    {v : NNReal} (hv : v ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v) P) (hXY : IndepFun X Y P) :
    HasLaw (fun ω => varianceRatio (X ω) (Y ω)) (snedecorFMeasure (m - 1) (n - 1)) P := by
  have hv0 : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  simpa [div_self hv0] using hasLaw_varianceRatio_div hm hn μ₁ μ₂ hv hv hX hY hXY

private lemma snedecorFMeasure_singleton' (d₁ d₂ : ℕ) (x : ℝ) : snedecorFMeasure d₁ d₂ {x} = 0 :=
  withDensity_absolutelyContinuous _ _ Real.volume_singleton

private lemma snedecorFMeasure_Iic_zero (d₁ d₂ : ℕ) : snedecorFMeasure d₁ d₂ (Set.Iic 0) = 0 := by
  rw [snedecorFMeasure, withDensity_apply _ measurableSet_Iic]
  refine (setLIntegral_congr_fun measurableSet_Iic fun x (hx : x ≤ 0) => ?_).trans
    (lintegral_zero)
  simp [not_lt.mpr hx]

/-- **Exact size of the one-sided variance-ratio `F` test.** Under `H₀ : v₁ = v₂`, rejecting when
`S_X² / S_Y² > q_{F(m-1,n-1)}(1 - α)` has probability exactly `α`. -/
theorem varianceRatio_test_size_eq {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (μ₁ μ₂ : ℝ)
    {v : NNReal} (hv : v ≠ 0) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v) P) (hXY : IndepFun X Y P) :
    P.real {ω | cdfQuantile (snedecorFMeasure (m - 1) (n - 1)) (1 - α) <
        varianceRatio (X ω) (Y ω)} = α := by
  have := isProbabilityMeasure_snedecorFMeasure (d₁ := m - 1) (d₂ := n - 1) (by omega)
    (by omega)
  have hR := hasLaw_varianceRatio hm hn μ₁ μ₂ hv hX hY hXY
  have hu : 1 - α ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have h := hR.measureReal_eq
    (p := fun t => t ∈ Set.Ioi (cdfQuantile (snedecorFMeasure (m - 1) (n - 1)) (1 - α)))
    measurableSet_Ioi
  rw [Set.ofPred_mem_eq] at h
  refine h.trans ?_
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_cdfQuantile_of_noAtom (snedecorFMeasure_singleton' _ _) hu]
  ring

/-- **Exact confidence interval for a variance ratio** (Lehmann–Romano, §5.3; inversion of
the `F` pivot). With `a = q_{F(m-1,n-1)}(α/2)` and `b = q_{F(m-1,n-1)}(1 - α/2)`, the interval
`[R / b, R / a]`, `R = S_X² / S_Y²`, covers `v₁ / v₂` with probability exactly `1 - α`. -/
theorem varianceRatio_interval_coverage_eq {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (μ₁ μ₂ : ℝ)
    {v₁ v₂ : NNReal} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin m → ℝ} {Y : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ => gaussianReal μ₁ v₁) P)
    (hY : HasLaw Y (Measure.pi fun _ => gaussianReal μ₂ v₂) P) (hXY : IndepFun X Y P) :
    P.real {ω | varianceRatio (X ω) (Y ω) /
          cdfQuantile (snedecorFMeasure (m - 1) (n - 1)) (1 - α / 2) ≤ (v₁ : ℝ) / v₂ ∧
        (v₁ : ℝ) / v₂ ≤ varianceRatio (X ω) (Y ω) /
          cdfQuantile (snedecorFMeasure (m - 1) (n - 1)) (α / 2)} = 1 - α := by
  set ν := snedecorFMeasure (m - 1) (n - 1)
  have := isProbabilityMeasure_snedecorFMeasure (d₁ := m - 1) (d₂ := n - 1) (by omega)
    (by omega)
  have hR := hasLaw_varianceRatio_div hm hn μ₁ μ₂ hv₁ hv₂ hX hY hXY
  have hlo : α / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hhi : 1 - α / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  set a := cdfQuantile ν (α / 2)
  set b := cdfQuantile ν (1 - α / 2)
  have ha : cdf ν a = α / 2 := cdf_cdfQuantile_of_noAtom (snedecorFMeasure_singleton' _ _) hlo
  have hb : cdf ν b = 1 - α / 2 :=
    cdf_cdfQuantile_of_noAtom (snedecorFMeasure_singleton' _ _) hhi
  have hcdf0 : cdf ν 0 = 0 := by
    rw [cdf_eq_real, measureReal_def, snedecorFMeasure_Iic_zero, ENNReal.toReal_zero]
  have hapos : 0 < a := by
    by_contra h
    have := (cdfQuantile_le_iff ν hlo).mp (not_lt.mp h)
    linarith [hα.1]
  have hab : a ≤ b := cdfQuantile_monoOn ν hlo hhi (by linarith [hα.2])
  have hbpos : 0 < b := hapos.trans_le hab
  have hr : (0 : ℝ) < (v₁ : ℝ) / v₂ :=
    div_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv₁))
      (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv₂))
  have h := hR.measureReal_eq (p := fun t => t ∈ Set.Icc a b) measurableSet_Icc
  rw [Set.ofPred_mem_eq, measureReal_Icc_of_noAtom (snedecorFMeasure_singleton' _ _) hab, ha,
    hb] at h
  refine Eq.trans ?_ (h.trans (by ring))
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  rw [div_le_iff₀ hbpos, le_div_iff₀ hapos, le_div_iff₀ hr, div_le_iff₀ hr]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### Large-sample transfer by Slutsky's theorem -/

private lemma div_mul_div_div_eq (A r s σ : ℝ) (hσ : σ ≠ 0) :
    A / (σ * r) / (s / σ) = A / (s * r) := by
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  linear_combination (A * r⁻¹ * s⁻¹) * inv_mul_cancel₀ hσ

private lemma measurable_pooledVariance {m n : ℕ} :
    Measurable fun p : (Fin m → ℝ) × (Fin n → ℝ) => pooledVariance p.1 p.2 := by
  unfold pooledVariance
  fun_prop

/-- **Slutsky transfer for the pooled two-sample `t` statistic** (van der Vaart, Lemma 2.8).
Along any filter of sample sizes `(m N, n N)`, if the known-variance statistic
`(X̄ - Ȳ - δ) / (σ √(1/m + 1/n))` converges in distribution to `Z` and the pooled variance
converges in probability to `σ² > 0`, then the pooled `t` statistic converges in distribution to
the same `Z`. With `Z ~ N(0, 1)` from a central limit theorem and `S_p² → σ²` from a law of large
numbers, this is the large-sample validity of the pooled `t` test without normality; both inputs
are hypotheses here. -/
theorem tendstoInDistribution_twoSampleTStatistic {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {m n : ι → ℕ} {X : ∀ N, Ω → Fin (m N) → ℝ} {Y : ∀ N, Ω → Fin (n N) → ℝ}
    (hX : ∀ N, AEMeasurable (X N) P) (hY : ∀ N, AEMeasurable (Y N) P)
    {δ σ : ℝ} (hσ : 0 < σ) {Z : Ω' → ℝ}
    (hZ : TendstoInDistribution (fun N ω => ((∑ i, X N ω i) / m N - (∑ j, Y N ω j) / n N - δ) /
      (σ * √(1 / m N + 1 / n N))) l Z (fun _ => P) P')
    (hS : TendstoInMeasure P (fun N ω => pooledVariance (X N ω) (Y N ω)) l (fun _ => σ ^ 2)) :
    TendstoInDistribution (fun N ω => twoSampleTStatistic δ (X N ω) (Y N ω)) l Z
      (fun _ => P) P' := by
  have hR : TendstoInMeasure P (fun N ω => √(pooledVariance (X N ω) (Y N ω)) / σ) l
      (fun _ => 1) := by
    have h := hS.comp_const_of_continuousAt (f := fun s => √s / σ)
      ((Real.continuous_sqrt.div_const σ).continuousAt)
    simpa [Real.sqrt_sq hσ.le, hσ.ne'] using h
  have hRm : ∀ N, AEMeasurable (fun ω => √(pooledVariance (X N ω) (Y N ω)) / σ) P := fun N =>
    ((measurable_pooledVariance.comp_aemeasurable ((hX N).prodMk (hY N))).sqrt).div_const σ
  refine (hZ.div_of_tendstoInMeasure_const one_ne_zero hR hRm).congr (fun N => ae_of_all _
    fun ω => ?_) (ae_of_all _ fun ω => div_one (Z ω))
  have hq : (0 : ℝ) ≤ 1 / m N + 1 / n N := by positivity
  dsimp only
  rw [twoSampleTStatistic, Real.sqrt_mul' _ hq, div_mul_div_div_eq _ _ _ _ hσ.ne']

end ProbabilityTheory

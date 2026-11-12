/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
public import MathlibExt.Probability.Distributions.ChiSquare
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw

/-!
# Genomic control: when dividing by `λ` calibrates association tests

Genomic control (Devlin and Roeder 1999) corrects a genome-wide association scan for
population structure by dividing every 1-df association statistic `χ²_j` by one inflation
factor `λ` estimated from the genome-wide distribution of the statistics, then comparing
`χ²_j / λ` with the usual `χ²₁` critical value. The distributional results here are generic
Gaussian-rescaling lemmas: they assume the exact score law and derive the corrected tail.
They do not derive that law from ancestry, relatedness, stratification, or a sampling model.
The separate LD-score results below concern expectations, not exact tail calibration.

## Gaussian distributional assumptions

`CommonInflationModel P ι` packages an assumed family `ι` of centered Gaussian scores on a
sample space with measure `P`:

* **Common variance.** Every score is assumed to have the same positive variance `λ`.
  No mechanism causing that variance is specified.
* **Exact Gaussian law.** The hypothesis is `Z_j ∼ 𝒩(0, λ)` (`HasLaw`), not a conclusion
  derived from a sample-size condition or a limit theorem. Only each marginal law is used;
  no independence between scores is assumed.
* **Known `λ`.** The correction divides by the assumed variance `λ`. Error from estimating
  `λ` (by the median or the mean of the observed statistics) is not covered.

The 1-df statistic is `χ²_j = Z_j ²`, and its tail is
`chiSqOneTail c = chiSquareMeasure 1 (Set.Ioi c)`, the probability that a `χ²₁` variable
exceeds `c`.

## Main results

Calibration inside the model:

* `CommonInflationModel.measure_reject_eq`: `P(χ²_j / λ > c) = chiSqOneTail c` for every
  threshold `c`, so a level-`α` critical value gives type I error exactly `α`
  (`CommonInflationModel.typeI_eq`).
* `CommonInflationModel.chiSqOneTail_lt_measure_reject_uncorrected`: without the correction, a
  real inflation `λ > 1` makes the uncorrected test strictly anti-conservative.

Failure outside the model:

* `measure_reject_eq_chiSqOneTail`: a score with law `𝒩(0, v)` divided by `k > 0` has
  tail `chiSqOneTail (c k / v)`; calibration needs `v = k`.
* `chiSqOneTail_lt_measure_reject_of_lt`, `measure_reject_lt_chiSqOneTail_of_gt`: a marker
  whose null variance `v` differs from the `λ` used is strictly anti-conservative when
  `v > λ` and strictly conservative when `v < λ`. These results still assume an exact
  Gaussian score law; no ancestry or stratification mechanism is derived.
* `chiSqOneTail_lt_of_lt`: the `χ²₁` tail is strictly decreasing on `[0, ∞)`, which drives
  both strict inequalities.

Moment calibration, reusing `LDScoreInflation`. In the LD-score model with a fixed
stratification shift (`LDScoreInflation.chiSqStrat`), take `lambdaGC` to be the mean expected
statistic (the population version of the mean-based estimator of `λ`):

* `integral_chiSqStrat_div_lambdaGC_of_null`: with no polygenic signal (`h² = 0`) and a
  stratification term `a` common to all markers, `λ_GC = 1 + N a` and every marker has
  `𝔼[χ²_j] / λ_GC = 1`.
* `integral_chiSqStrat_div_lambdaGC_eq_one_iff`: with polygenic signal `h² ≠ 0`,
  `𝔼[χ²_j] / λ_GC = 1` holds exactly for the markers whose LD score equals the mean LD score.
  By `integral_chiSqStrat_sub_lambdaGC`, markers below the mean LD score get a ratio below `1`
  (over-corrected, `integral_chiSqStrat_div_lambdaGC_lt_one_of_lt`) and markers above it a ratio
  above `1` (under-corrected, `one_lt_integral_chiSqStrat_div_lambdaGC_of_lt`): genomic control
  absorbs polygenic signal into `λ`. With `h² ≠ 0` no marker is null, so these are
  statements about the expected statistic, not about type I error.
* `not_exists_lambda_calibrates_of_strat_ne`: with `h² = 0` but stratification terms that
  differ between two markers, no single `λ` makes both expected statistics equal to `1`.

`LDScore.Model` fixes only second moments, so the stratified statistic of `LDScoreInflation`
need not be a scaled central `χ²₁` (under Gaussianity it is a scaled noncentral `χ²₁` whenever
`s · X_jᵀ c ≠ 0`, since the fixed shift then gives the score a nonzero mean); the moment results
therefore do not imply the distributional ones, which independently assume the exact
centered Gaussian laws above.

## Reuse and sources (API-00 receipt)

Reused, not redefined: `LDScore.Model`, `LDScore.ldScore`, `LDScore.IsStandardized`,
`LDScore.IsStandardized.ldCorr_self`, `LDScore.IsStandardized.one_le_ldScore`,
`LDScore.Model.h2_nonneg`, `LDScore.Model.h2_le_one`,
`ProbabilityTheory.chiSquareSurvival`,
`ProbabilityTheory.gaussianReal_sq_preimage_Ioi_eq_chiSquareSurvival`,
`LDScoreInflation.chiSqStrat`, `LDScoreInflation.meanLDScore`,
`LDScoreInflation.integral_chiSqStrat_of_standardized`,
`LDScoreInflation.mean_integral_chiSqStrat_of_const`; from Mathlib, `gaussianReal`,
`ProbabilityTheory.HasLaw`, `gaussianReal_div_const`, `gaussianReal_absolutelyContinuous'`.
A search of `MathlibExt` and `WantedExt` for genomic control, `λ_GC`, and inflation-factor
calibration found no existing development; `Eigenstrat` corrects by principal components, a
different method.

## References

* B. Devlin and K. Roeder, *Genomic control for association studies*, Biometrics 55 (1999),
  997–1004.
* B. K. Bulik-Sullivan et al., *LD Score regression distinguishes confounding from
  polygenicity in genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
open scoped NNReal ENNReal

namespace MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControl

/-! ### The `χ²₁` tail -/

/-- The `χ²₁` tail `P(χ²₁ > c)`, as the canonical chi-square survival function. -/
noncomputable def chiSqOneTail (c : ℝ) : ℝ≥0∞ := chiSquareSurvival 1 c

/-- Bridge to the Gaussian form, for proofs that work with a standard-normal square. -/
theorem chiSqOneTail_eq_gaussianReal (c : ℝ) :
    chiSqOneTail c = gaussianReal 0 1 {x | c < x ^ 2} :=
  (gaussianReal_sq_preimage_Ioi_eq_chiSquareSurvival c).symm

/-- The `χ²₁` tail is strictly decreasing on `[0, ∞)`: for `0 ≤ a < b`, the interval
`(√a, √b)` has positive standard-normal mass and lies in `{a < x²} \ {b < x²}`. -/
theorem chiSqOneTail_lt_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    chiSqOneTail b < chiSqOneTail a := by
  rw [chiSqOneTail_eq_gaussianReal, chiSqOneTail_eq_gaussianReal]
  have hsq : √a < √b := Real.sqrt_lt_sqrt ha hab
  set I := Set.Ioo (√a) (√b) with hI
  have hIpos : gaussianReal 0 1 I ≠ 0 := by
    intro h0
    have hvol := gaussianReal_absolutelyContinuous' (0 : ℝ) (one_ne_zero : (1 : ℝ≥0) ≠ 0) h0
    rw [hI, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hvol
    linarith
  have hmemI : ∀ x ∈ I, a < x ^ 2 ∧ x ^ 2 < b := fun x hx => by
    have h0 : 0 ≤ √a := Real.sqrt_nonneg a
    have hx0 : 0 < x := lt_of_le_of_lt h0 hx.1
    refine ⟨(Real.sqrt_lt' hx0).1 hx.1, (Real.lt_sqrt hx0.le).1 hx.2⟩
  have hdisj : Disjoint {x : ℝ | b < x ^ 2} I :=
    Set.disjoint_left.2 fun x hb hx => absurd hb (not_lt.2 (hmemI x hx).2.le)
  have hsub : {x : ℝ | b < x ^ 2} ∪ I ⊆ {x | a < x ^ 2} := by
    rintro x (hx | hx)
    · exact lt_trans hab hx
    · exact (hmemI x hx).1
  calc gaussianReal 0 1 {x | b < x ^ 2}
        < gaussianReal 0 1 {x | b < x ^ 2} + gaussianReal 0 1 I :=
        ENNReal.lt_add_right (measure_ne_top _ _) hIpos
    _ = gaussianReal 0 1 ({x : ℝ | b < x ^ 2} ∪ I) :=
        (measure_union hdisj measurableSet_Ioo).symm
    _ ≤ gaussianReal 0 1 {x | a < x ^ 2} := measure_mono hsub

/-! ### Rejection probability of a rescaled Gaussian score -/

/-- A score with law `𝒩(0, v)`, `v ≠ 0`, divided by `k > 0`: the rejection probability of
`Z² / k > c` is the `χ²₁` tail at `c k / v`. -/
theorem measure_reject_eq_chiSqOneTail {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
    {Z : Ω → ℝ} {v : ℝ≥0} (hv : v ≠ 0) (hZ : HasLaw Z (gaussianReal 0 v) P) {k : ℝ}
    (hk : 0 < k) (c : ℝ) :
    P {ω | c < Z ω ^ 2 / k} = chiSqOneTail (c * k / v) := by
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
  have hW := gaussianReal_div_const hZ (√(v : ℝ))
  rw [zero_div] at hW
  replace hW : HasLaw (fun ω => Z ω / √(v : ℝ)) (gaussianReal 0 1) P := by
    convert hW using 2
    ext
    simp [Real.sq_sqrt hv0.le, hv0.ne']
  have hset : {ω | c < Z ω ^ 2 / k} = {ω | c * k / v < (Z ω / √(v : ℝ)) ^ 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, div_pow, Real.sq_sqrt hv0.le]
    rw [lt_div_iff₀ hk, div_lt_div_iff_of_pos_right hv0]
  rw [hset, hW.measure_eq (p := fun x => c * k / v < x ^ 2)
    (measurableSet_lt measurable_const (by fun_prop)), chiSqOneTail_eq_gaussianReal]

/-! ### Calibration conditional on exact Gaussian score laws -/

/-- A family of scores assumed to have centered Gaussian laws with a common positive variance.
The field `hasLaw_score` is a distributional hypothesis, not a result derived from a
population-structure or sampling model. The calibration lemmas below are consequences of
Gaussian rescaling; they do not justify that hypothesis for association statistics. -/
structure CommonInflationModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ι : Type*) where
  /-- The common inflation factor `λ` of the null variance. -/
  lam : ℝ≥0
  /-- The inflation factor is nonzero. -/
  lam_ne_zero : lam ≠ 0
  /-- The null score of each marker; its 1-df statistic is `score j ^ 2`. -/
  score : ι → Ω → ℝ
  /-- Each null score has law `𝒩(0, λ)`. -/
  hasLaw_score : ∀ j, HasLaw (score j) (gaussianReal 0 lam) P

namespace CommonInflationModel

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} (G : CommonInflationModel P ι)

/-- The common inflation factor is positive. -/
theorem lam_pos : (0 : ℝ) < G.lam :=
  lt_of_le_of_ne G.lam.2 (by exact_mod_cast G.lam_ne_zero.symm)

/-- Genomic control is exactly calibrated in the model: for every null marker and threshold `c`,
`P(χ²_j / λ > c)` is the `χ²₁` tail at `c`. -/
theorem measure_reject_eq (j : ι) (c : ℝ) :
    P {ω | c < G.score j ω ^ 2 / G.lam} = chiSqOneTail c := by
  rw [measure_reject_eq_chiSqOneTail G.lam_ne_zero (G.hasLaw_score j) G.lam_pos,
    mul_div_cancel_right₀ _ G.lam_pos.ne']

/-- Type I error control: if `c` is the level-`α` critical value of `χ²₁`, the genomic-control
test rejects a null marker with probability exactly `α`. -/
theorem typeI_eq {α : ℝ≥0∞} {c : ℝ} (hc : chiSqOneTail c = α) (j : ι) :
    P {ω | c < G.score j ω ^ 2 / G.lam} = α := by
  rw [G.measure_reject_eq j c, hc]

/-- Without the correction, real inflation `λ > 1` makes the test strictly anti-conservative at
every positive threshold. -/
theorem chiSqOneTail_lt_measure_reject_uncorrected (hlam : 1 < (G.lam : ℝ)) (j : ι) {c : ℝ}
    (hc : 0 < c) : chiSqOneTail c < P {ω | c < G.score j ω ^ 2} := by
  have h := measure_reject_eq_chiSqOneTail G.lam_ne_zero (G.hasLaw_score j) one_pos c
  simp only [div_one, mul_one] at h
  rw [h]
  exact chiSqOneTail_lt_of_lt (div_nonneg hc.le G.lam.2) (div_lt_self hc hlam)

end CommonInflationModel

/-! ### Failure outside the model: marker-specific inflation -/

/-- A marker whose null variance `v` exceeds the `λ` used (its inflation is not the common one)
is strictly anti-conservative after genomic control, at every positive threshold. -/
theorem chiSqOneTail_lt_measure_reject_of_lt {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) {lam : ℝ}
    (hlam : 0 < lam) (hv : lam < v) {c : ℝ} (hc : 0 < c) :
    chiSqOneTail c < P {ω | c < Z ω ^ 2 / lam} := by
  have hv0 : (0 : ℝ) < v := hlam.trans hv
  rw [measure_reject_eq_chiSqOneTail (by exact_mod_cast hv0.ne') hZ hlam]
  refine chiSqOneTail_lt_of_lt (by positivity) ?_
  rw [div_lt_iff₀ hv0]
  exact mul_lt_mul_of_pos_left hv hc

/-- A marker whose null variance `v` is below the `λ` used is strictly conservative after
genomic control, at every positive threshold. -/
theorem measure_reject_lt_chiSqOneTail_of_gt {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hv0 : v ≠ 0) (hZ : HasLaw Z (gaussianReal 0 v) P)
    {lam : ℝ} (hv : (v : ℝ) < lam) {c : ℝ} (hc : 0 < c) :
    P {ω | c < Z ω ^ 2 / lam} < chiSqOneTail c := by
  have hv0' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv0.symm)
  rw [measure_reject_eq_chiSqOneTail hv0 hZ (hv0'.trans hv)]
  refine chiSqOneTail_lt_of_lt hc.le ?_
  rw [lt_div_iff₀ hv0']
  exact mul_lt_mul_of_pos_left hv hc

/-! ### Moment calibration in the LD-score model -/

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {N M : ℕ}

/-- The population genomic-control factor of the LD-score model with stratification: the mean
expected association statistic `(1 / M) ∑ j, 𝔼[χ²_j]`. -/
noncomputable def lambdaGC (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (s : ℝ)
    (c : Fin N → ℝ) : ℝ :=
  (∑ j, ∫ ω, chiSqStrat D X s c j ω ∂μ) / M

/-- With a stratification term `a` common to all markers, each expected statistic differs from
`λ_GC` by the polygenic term `N h² / M * (ℓ_j - ℓ̄)`. -/
theorem integral_chiSqStrat_sub_lambdaGC [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) (j : Fin M) :
    ∫ ω, chiSqStrat D X s c j ω ∂μ - lambdaGC D X s c =
      N * D.h2 / M * (ldScore X j - meanLDScore X) := by
  rw [lambdaGC, mean_integral_chiSqStrat_of_const D X hN hM hX hβ hε s c ha,
    integral_chiSqStrat_of_standardized D X hN hX hβ hε, ← ha j]
  ring

/-- Genomic control is calibrated in mean when there is no polygenic signal (`h² = 0`) and the
stratification term `a` is common to all markers: `λ_GC = 1 + N a`, and every marker has
`𝔼[χ²_j] / λ_GC = 1`. -/
theorem integral_chiSqStrat_div_lambdaGC_of_null [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (hh : D.h2 = 0)
    (s : ℝ) (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    lambdaGC D X s c = 1 + N * a ∧
      ∀ j, (∫ ω, chiSqStrat D X s c j ω ∂μ) / lambdaGC D X s c = 1 := by
  have hlam : lambdaGC D X s c = 1 + N * a := by
    rw [lambdaGC, mean_integral_chiSqStrat_of_const D X hN hM hX hβ hε s c ha, hh]
    ring
  have ha0 : 0 ≤ a := ha ⟨0, Nat.pos_of_ne_zero hM⟩ ▸ by positivity
  refine ⟨hlam, fun j => ?_⟩
  have hsub := integral_chiSqStrat_sub_lambdaGC D X hN hM hX hβ hε s c ha j
  rw [hh, mul_zero, zero_div, zero_mul, sub_eq_zero] at hsub
  rw [hsub, div_self (by rw [hlam]; positivity)]

/-- The polygenic slope `N h² / M` is positive when `N, M ≠ 0` and `h² ≠ 0`. -/
private theorem polygenicSlope_pos (D : Model μ N M) (hN : N ≠ 0) (hM : M ≠ 0)
    (hh : D.h2 ≠ 0) : (0 : ℝ) < N * D.h2 / M := by
  have hh0 : 0 < D.h2 := lt_of_le_of_ne (D.h2_nonneg (Nat.pos_of_ne_zero hM)) (Ne.symm hh)
  have := Nat.cast_pos (α := ℝ) |>.mpr (Nat.pos_of_ne_zero hN)
  have := Nat.cast_pos (α := ℝ) |>.mpr (Nat.pos_of_ne_zero hM)
  positivity

/-- With a common stratification term `a ≥ 0` and `h² ≠ 0`, `λ_GC > 0`. -/
theorem lambdaGC_pos [IsProbabilityMeasure μ] (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)
    (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X) (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0)
    (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (hh : D.h2 ≠ 0) (s : ℝ) (c : Fin N → ℝ) {a : ℝ}
    (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) : 0 < lambdaGC D X s c := by
  have hM0 : 0 < M := Nat.pos_of_ne_zero hM
  have ha0 : 0 ≤ a := ha ⟨0, hM0⟩ ▸ by positivity
  have hh1 : D.h2 ≤ 1 := D.h2_le_one (Nat.pos_of_ne_zero hN)
  have hl : 0 < meanLDScore X := by
    rw [meanLDScore]
    refine div_pos ?_ (Nat.cast_pos.mpr hM0)
    calc (0 : ℝ) < ldScore X ⟨0, hM0⟩ := lt_of_lt_of_le one_pos (hX.one_le_ldScore hN _)
      _ ≤ ∑ j, ldScore X j :=
        Finset.single_le_sum (fun k _ => le_trans zero_le_one (hX.one_le_ldScore hN k))
          (Finset.mem_univ _)
  rw [lambdaGC, mean_integral_chiSqStrat_of_const D X hN hM hX hβ hε s c ha]
  have := mul_pos (polygenicSlope_pos D hN hM hh) hl
  have : (0 : ℝ) ≤ N * a := by positivity
  linarith

/-- **Failure with polygenic signal.** With a common stratification term and `h² ≠ 0`,
genomic control calibrates a marker in mean exactly when its LD score equals the mean LD
score. With `h² ≠ 0` no marker is null, so "calibrated in mean" concerns the expected statistic,
not type I error. -/
theorem integral_chiSqStrat_div_lambdaGC_eq_one_iff [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (hh : D.h2 ≠ 0)
    (s : ℝ) (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a)
    (j : Fin M) :
    (∫ ω, chiSqStrat D X s c j ω ∂μ) / lambdaGC D X s c = 1 ↔ ldScore X j = meanLDScore X := by
  have hlam := lambdaGC_pos D X hN hM hX hβ hε hh s c ha
  have hsub := integral_chiSqStrat_sub_lambdaGC D X hN hM hX hβ hε s c ha j
  have hcoef := (polygenicSlope_pos D hN hM hh).ne'
  rw [div_eq_one_iff_eq hlam.ne', ← sub_eq_zero, hsub, mul_eq_zero, sub_eq_zero]
  exact or_iff_right hcoef

/-- With a common stratification term and `h² ≠ 0`, a marker whose LD score is below the mean
LD score is over-corrected in mean: `𝔼[χ²_j] / λ_GC < 1`. -/
theorem integral_chiSqStrat_div_lambdaGC_lt_one_of_lt [IsProbabilityMeasure μ]
    (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0)
    (hX : IsStandardized X) (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0)
    (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (hh : D.h2 ≠ 0) (s : ℝ) (c : Fin N → ℝ) {a : ℝ}
    (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) {j : Fin M}
    (hj : ldScore X j < meanLDScore X) :
    (∫ ω, chiSqStrat D X s c j ω ∂μ) / lambdaGC D X s c < 1 := by
  have hlam := lambdaGC_pos D X hN hM hX hβ hε hh s c ha
  have hsub := integral_chiSqStrat_sub_lambdaGC D X hN hM hX hβ hε s c ha j
  have hcoef := polygenicSlope_pos D hN hM hh
  rw [div_lt_one hlam]
  nlinarith [mul_neg_of_pos_of_neg hcoef (sub_neg.mpr hj)]

/-- With a common stratification term and `h² ≠ 0`, a marker whose LD score is above the mean
LD score is under-corrected in mean: `𝔼[χ²_j] / λ_GC > 1`. -/
theorem one_lt_integral_chiSqStrat_div_lambdaGC_of_lt [IsProbabilityMeasure μ]
    (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0)
    (hX : IsStandardized X) (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0)
    (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (hh : D.h2 ≠ 0) (s : ℝ) (c : Fin N → ℝ) {a : ℝ}
    (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) {j : Fin M}
    (hj : meanLDScore X < ldScore X j) :
    1 < (∫ ω, chiSqStrat D X s c j ω ∂μ) / lambdaGC D X s c := by
  have hlam := lambdaGC_pos D X hN hM hX hβ hε hh s c ha
  have hsub := integral_chiSqStrat_sub_lambdaGC D X hN hM hX hβ hε s c ha j
  have hcoef := polygenicSlope_pos D hN hM hh
  rw [one_lt_div hlam]
  nlinarith [mul_pos hcoef (sub_pos.mpr hj)]

/-- **Failure with heterogeneous stratification.** With no polygenic signal but stratification
terms that differ between two markers, no single `λ` calibrates both in mean. -/
theorem not_exists_lambda_calibrates_of_strat_ne [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (hh : D.h2 = 0)
    (s : ℝ) (c : Fin N → ℝ) {j k : Fin M}
    (hjk : s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 ≠ s ^ 2 * ((∑ i, X i k * c i) / N) ^ 2) :
    ¬ ∃ lam : ℝ, (∫ ω, chiSqStrat D X s c j ω ∂μ) / lam = 1 ∧
      (∫ ω, chiSqStrat D X s c k ω ∂μ) / lam = 1 := by
  rintro ⟨lam, hj, hk⟩
  have hlam : lam ≠ 0 := by
    rintro rfl
    simp at hj
  rw [div_eq_one_iff_eq hlam, integral_chiSqStrat_of_standardized D X hN hX hβ hε, hh] at hj hk
  apply hjk
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have := hj.trans hk.symm
  have h2 : (N : ℝ) * (s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2) =
      N * (s ^ 2 * ((∑ i, X i k * c i) / N) ^ 2) := by linear_combination this
  exact mul_left_cancel₀ hNr h2

end MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControl

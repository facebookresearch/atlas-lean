/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.GenomicPrediction
public import MathlibExt.Probability.Statistics.Slutsky
public import MathlibExt.Probability.Distributions.ChiSquare
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.Integration

/-!
# The Cochran–Armitage trend test is asymptotically `χ²₁`

The **Cochran–Armitage trend test** for a case–control genotype table (Cochran 1954, Armitage
1955) compares the case proportions of the ordered genotype classes `0, 1, 2` (copies of the
counted allele) along the linear score `i`. The finite-sample statistic is
`GenomicPrediction.ArmitageTrend.trendStat`,
`N U² / (R S (N ∑ i² n_i - (∑ i n_i)²))` with `U = ∑ i i (r_i S - s_i R)`, and
`GenomicPrediction.ArmitageTrend.trendStat_eq_total_mul_corrSq` shows it equals `N r²`, where
`r` is the sample correlation of case status and genotype score. This file proves its
large-sample null law.

## Null model and asymptotic index

Subjects `m = 0, 1, 2, …` are i.i.d. pairs `S m = (G m, Y m) : Fin 3 × Bool` of a genotype class
and a case indicator (*multinomial sampling*: the counts of the first `N` subjects in the six
cells of the `2 × 3` table are multinomial). The **null** is independence of genotype and case
status, `G 0 ⟂ Y 0`, so the cell probabilities are `π_i p` (cases) and `π_i (1 - p)` (controls),
with `p = P(Y 0 = true)` and `π_i = P(G 0 = i)`. The asymptotic index is the number `N` of
subjects, with `p` and `π` fixed.

This is prospective (cross-sectional) sampling: the numbers of cases `R` and controls `S` are
random. The usual case–control design fixes `R` and `S` and samples genotypes within each group
(product-binomial sampling); that design is **not** covered here.

## Fitted parameters and degrees of freedom

The `2 × 3` multinomial has `5` free cell probabilities. The null fits `3` of them: the case
fraction `p` (by `R / N`) and two genotype frequencies `π₀, π₁` (they enter through the sample
mean and variance of the score). The omnibus test of independence therefore has `5 - 3 = 2`
degrees of freedom. The trend statistic is a single contrast, along the centered score
direction, so it has **one** degree of freedom: `tendstoInDistribution_caStat` proves the limit
law is `chiSquareMeasure 1` *with all three parameters fitted*. Fitting costs the trend contrast
nothing because the centered score is orthogonal to the fitted directions: the oracle statistic
with `p`, `π` known has the same limit (`tendstoInDistribution_caOracleStat`, the genotype-table
instance of the generic `tendstoInDistribution_oracleStat`), and the difference
of the scaled numerators tends to `0` in probability (the `√N (Ā - μ_A)(B̄ - μ_B)` term in the
proof).

## Regime conditions and boundary cases

* **Non-degeneracy.** The theorem assumes `0 < p < 1` and a positive score variance
  `Var[score (G 0)] > 0`, i.e. at least two genotype classes have positive probability. Every
  cell with `π_i > 0` then has expected count `N π_i p → ∞` and `N π_i (1 - p) → ∞`; cells with
  `π_i = 0` stay empty almost surely and do not matter.
* **Singular design.** If the genotype is almost surely a single class (zero score variance),
  the score direction is degenerate: the statistic is `0` almost surely for every `N`
  (`caStat_ae_eq_zero_of_genotype_const`, from the finite identity
  `trendStat_eq_zero_of_single_genotype`), so it converges to the Dirac mass at `0` and **not**
  to `χ²₁` (`not_tendstoInDistribution_caStat_of_genotype_const`). Likewise a table without
  cases or without controls has statistic `0` (`trendStat_eq_zero_of_no_cases`,
  `trendStat_eq_zero_of_no_controls`).
* **Small cells.** For fixed finite `N` the statistic has a discrete law and the `χ²₁` law is
  only a limit. The test file computes the three tables with a single case among `100` subjects
  of genotype counts `(81, 18, 1)`: the case in class `2` gives `200 / 11 ≈ 18.2`, the unique
  largest value (the others give `200 / 891` and `3200 / 891`). Under the null, given the
  margins, the case is equally likely to be any of the `100` subjects, so that table has
  conditional probability `1/100`, far above its `χ²₁` tail; this permutation probability is
  stated, not formalized.
* **Fitted allele frequency.** Replacing the observed score variance by the Hardy–Weinberg
  variance `2 p̂ q̂` of a fitted allele frequency gives the allelic test; for nondegenerate margins
  (cases and controls present, `0 < p̂ < 1`, positive score variance) and trend numerator
  `U ≠ 0`, it agrees with the trend test iff the pooled sample is in Hardy–Weinberg proportions
  (`GenomicPrediction.ArmitageTrend.allelicStat_eq_trendStat_iff`). When `U = 0` both statistics
  are `0` whatever the proportions. The trend test fits the
  genotype frequencies directly and needs no Hardy–Weinberg assumption; this file does not treat
  the allelic test asymptotically.

## Main results

* `tendstoInDistribution_mul_sampleCorrSq`: for i.i.d. square-integrable real pairs `(A, B)`
  with `A ⟂ B` and positive variances, `N r_N² → χ²₁` in distribution.
* `tendstoInDistribution_oracleStat`: the same limit for the oracle statistic with known means
  and variances.
* `caStat_eq_mul_sampleCorrSq`: the Cochran–Armitage statistic of the first `N` subjects is
  `N r_N²` for the genotype score and case indicator.
* `tendstoInDistribution_caStat`: **the Cochran–Armitage trend test is asymptotically `χ²₁`**
  under the multinomial independence null.
* `tendstoInDistribution_caOracleStat`: the same limit for the trend statistic with `p` and the
  genotype frequencies known.
* `not_tendstoInDistribution_caStat_of_genotype_const`: the singular design has no `χ²₁` limit.
* `trendStat_eq_zero_of_single_genotype`, `trendStat_eq_zero_of_no_cases`,
  `trendStat_eq_zero_of_no_controls`: degenerate finite tables.

## Source receipt

The statistic is the one already formalized in `GenomicPrediction.ArmitageTrend` (scores
`0, 1, 2`), reused here unchanged. Armitage (1955) refers `χ² = N r²` to `χ²₁` in large
samples; Sasieni (1997) restates the trend test as `N r²` and compares it with the allelic test.
The proof is the standard central limit theorem + strong law + Slutsky argument (van der Vaart
1998, Lemma 2.8 for Slutsky), using Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub` and
`strong_law_ae_real`.

## References

* W. G. Cochran, *Some methods for strengthening the common χ² tests*, Biometrics 10 (1954),
  417–451.
* P. Armitage, *Tests for linear trends in proportions and frequencies*, Biometrics 11 (1955),
  375–386.
* P. D. Sasieni, *From genotypes to genes: doubling the sample size*, Biometrics 53 (1997),
  1253–1261.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace MathlibExt.Biology.StatisticalGenetics.CochranArmitage

open MathlibExt.Biology.StatisticalGenetics.GenomicPrediction

/-! ### Sample moments -/

/-- The sample mean `(∑_{m < N} f m) / N` of the first `N` terms of `f`. -/
noncomputable def sampleMean (f : ℕ → ℝ) (N : ℕ) : ℝ := (∑ m ∈ range N, f m) / N

/-- The squared sample correlation of the first `N` pairs `(a m, b m)`, in moment form:
`(mean(ab) - mean(b) mean(a))² / ((mean(b²) - mean(b)²) (mean(a²) - mean(a)²))`. Where a sample
variance vanishes the value is `0`, by `x / 0 = 0`. -/
noncomputable def sampleCorrSq (a b : ℕ → ℝ) (N : ℕ) : ℝ :=
  (sampleMean (fun m ↦ a m * b m) N - sampleMean b N * sampleMean a N) ^ 2 /
    ((sampleMean (fun m ↦ b m ^ 2) N - sampleMean b N ^ 2) *
      (sampleMean (fun m ↦ a m ^ 2) N - sampleMean a N ^ 2))

/-! ### Asymptotics of `N r²` under independence -/

section Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Convergence in distribution depends on the limit only through its law. -/
private theorem tendstoInDistribution_of_hasLaw {Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₂]
    [MeasurableSpace Ω₃] {P₂ : Measure Ω₂} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₂]
    [IsProbabilityMeasure P₃] {T : ℕ → Ω → ℝ} {Y : Ω₂ → ℝ} {Z : Ω₃ → ℝ} {ρ : Measure ℝ}
    (h : TendstoInDistribution T atTop Y (fun _ ↦ P) P₂) (hY : HasLaw Y ρ P₂)
    (hZ : HasLaw Z ρ P₃) :
    TendstoInDistribution T atTop Z (fun _ ↦ P) P₃ where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    convert h.tendsto using 3
    exact congrArg 𝓝 (Subtype.ext (hZ.map_eq.trans hY.map_eq.symm))

/-- Under the standard Gaussian, `x ↦ √c x` has law `N(0, c)`. -/
private theorem hasLaw_sqrt_mul {c : ℝ} (hc : 0 ≤ c) :
    HasLaw (fun x : ℝ ↦ √c * x) (gaussianReal 0 c.toNNReal) (gaussianReal 0 1) where
  aemeasurable := by fun_prop
  map_eq := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt hc, Real.coe_toNNReal _ hc]

variable {X : ℕ → Ω → ℝ × ℝ}

omit [IsProbabilityMeasure P] in
/-- A measurable function of an i.i.d. sequence obeys the strong law of large numbers. -/
private theorem ae_tendsto_sampleMean (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P) {φ : ℝ × ℝ → ℝ} (hφ : Measurable φ)
    (hint : Integrable (fun ω ↦ φ (X 0 ω)) P) :
    ∀ᵐ ω ∂P, Tendsto (fun N ↦ sampleMean (fun m ↦ φ (X m ω)) N) atTop
      (𝓝 (∫ ω, φ (X 0 ω) ∂P)) :=
  strong_law_ae_real (fun m ω ↦ φ (X m ω)) hint
    (fun _ _ hij ↦ (hindep.indepFun hij).comp hφ hφ) (fun m ↦ (hident m).comp hφ)

/-- The central limit theorem for a measurable function of an i.i.d. sequence, with the limit
`√(Var) x` under the standard Gaussian. -/
private theorem tendstoInDistribution_clt (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P) {φ : ℝ × ℝ → ℝ} (hφ : Measurable φ)
    (hL2 : MemLp (fun ω ↦ φ (X 0 ω)) 2 P) :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ (√N)⁻¹ * (∑ m ∈ range N, φ (X m ω) - N * ∫ ω, φ (X 0 ω) ∂P)) atTop
      (fun x : ℝ ↦ √(Var[fun ω ↦ φ (X 0 ω); P]) * x) (fun _ ↦ P) (gaussianReal 0 1) :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun m ω ↦ φ (X m ω))
    (hasLaw_sqrt_mul (variance_nonneg _ _)) hL2 (hindep.comp (fun _ ↦ φ) fun _ ↦ hφ)
    (fun m ↦ (hident m).comp hφ)

/-- The exact decomposition of the scaled sample covariance:
`√N (mean(ab) - mean(b) mean(a)) = N^{-1/2} ∑ (a - μ)(b - ν) - N^{-1/2} (∑ a - N μ) (mean(b) - ν)`.
It holds for every `N`, including `N = 0` where all three terms are `0`. -/
private theorem sqrt_mul_cov_eq (a b : ℕ → ℝ) (μ ν : ℝ) (N : ℕ) :
    √N * (sampleMean (fun m ↦ a m * b m) N - sampleMean b N * sampleMean a N) =
      (√N)⁻¹ * (∑ m ∈ range N, (a m - μ) * (b m - ν) - N * 0) +
        ((√N)⁻¹ * (∑ m ∈ range N, a m - N * μ)) * (ν - sampleMean b N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hs : (√N : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hN)
  have hss : (√N : ℝ) * √N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hsum : ∑ m ∈ range N, (a m - μ) * (b m - ν) =
      ∑ m ∈ range N, a m * b m - ν * ∑ m ∈ range N, a m - μ * ∑ m ∈ range N, b m +
        N * (μ * ν) := by
    simp only [sub_mul, mul_sub, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      ← mul_sum, ← sum_mul]
    ring
  rw [hsum]
  simp only [sampleMean]
  generalize ∑ m ∈ range N, a m * b m = sab
  generalize ∑ m ∈ range N, a m = sa
  generalize ∑ m ∈ range N, b m = sb
  generalize √(N : ℝ) = t at hs hss ⊢
  rw [← hss]
  field_simp
  ring

/-- The CLT for the centered product `(A - μ_A)(B - μ_B)` of independent coordinates: it has
mean `0` and variance `Var A · Var B`, so its scaled sum is asymptotically `N(0, Var A · Var B)`. -/
private theorem tendstoInDistribution_centered (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P)
    (hnull : IndepFun (fun ω ↦ (X 0 ω).1) (fun ω ↦ (X 0 ω).2) P)
    (hA : MemLp (fun ω ↦ (X 0 ω).1) 2 P) (hB : MemLp (fun ω ↦ (X 0 ω).2) 2 P) :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ (√N)⁻¹ * (∑ m ∈ range N,
        ((X m ω).1 - ∫ ω, (X 0 ω).1 ∂P) * ((X m ω).2 - ∫ ω, (X 0 ω).2 ∂P) - N * 0)) atTop
      (fun x : ℝ ↦ √(Var[fun ω ↦ (X 0 ω).1; P] * Var[fun ω ↦ (X 0 ω).2; P]) * x)
      (fun _ ↦ P) (gaussianReal 0 1) := by
  set μA := ∫ ω, (X 0 ω).1 ∂P with hμA
  set μB := ∫ ω, (X 0 ω).2 ∂P with hμB
  set vA := Var[fun ω ↦ (X 0 ω).1; P] with hvA_def
  set vB := Var[fun ω ↦ (X 0 ω).2; P] with hvB_def
  have hXm : ∀ m, AEMeasurable (X m) P := fun m ↦ (hident m).aemeasurable_fst
  have hAm : ∀ m, AEMeasurable (fun ω ↦ (X m ω).1) P := fun m ↦ (hXm m).fst
  have hBm : ∀ m, AEMeasurable (fun ω ↦ (X m ω).2) P := fun m ↦ (hXm m).snd
  -- The centered product `W = (A - μA)(B - μB)`: mean `0`, variance `vA vB`.
  set φW : ℝ × ℝ → ℝ := fun x ↦ (x.1 - μA) * (x.2 - μB) with hφW
  have hφW_meas : Measurable φW := by fun_prop
  have hcA : IndepFun (fun ω ↦ (X 0 ω).1 - μA) (fun ω ↦ (X 0 ω).2 - μB) P :=
    hnull.comp (φ := fun x ↦ x - μA) (ψ := fun x ↦ x - μB) (by fun_prop) (by fun_prop)
  have hcA2 : IndepFun (fun ω ↦ ((X 0 ω).1 - μA) ^ 2) (fun ω ↦ ((X 0 ω).2 - μB) ^ 2) P :=
    hnull.comp (φ := fun x ↦ (x - μA) ^ 2) (ψ := fun x ↦ (x - μB) ^ 2) (by fun_prop)
      (by fun_prop)
  have hAc : MemLp (fun ω ↦ (X 0 ω).1 - μA) 2 P := hA.sub (memLp_const μA)
  have hBc : MemLp (fun ω ↦ (X 0 ω).2 - μB) 2 P := hB.sub (memLp_const μB)
  have hmeanW : ∫ ω, φW (X 0 ω) ∂P = 0 := by
    simp only [hφW]
    rw [IndepFun.integral_fun_mul_eq_mul_integral hcA ((hAm 0).sub_const μA).aestronglyMeasurable
      ((hBm 0).sub_const μB).aestronglyMeasurable]
    rw [integral_sub (hA.integrable one_le_two) (integrable_const _), integral_const]
    simp [← hμA]
  have hW2 : Integrable (fun ω ↦ φW (X 0 ω) ^ 2) P := by
    refine (IndepFun.integrable_mul hcA2 hAc.integrable_sq hBc.integrable_sq).congr
      (ae_of_all _ fun ω ↦ ?_)
    simp [hφW, mul_pow]
  have hWL2 : MemLp (fun ω ↦ φW (X 0 ω)) 2 P :=
    (memLp_two_iff_integrable_sq (hφW_meas.comp_aemeasurable (hXm 0)).aestronglyMeasurable).2 hW2
  have hvarW : Var[fun ω ↦ φW (X 0 ω); P] = vA * vB := by
    rw [variance_eq_integral (X := fun ω ↦ φW (X 0 ω)) (hφW_meas.comp_aemeasurable (hXm 0)), hmeanW,
      hvA_def, hvB_def, variance_eq_integral (hAm 0), variance_eq_integral (hBm 0), ← hμA, ← hμB]
    simp only [sub_zero, hφW, mul_pow]
    exact IndepFun.integral_fun_mul_eq_mul_integral hcA2
      (((hAm 0).sub_const _).pow_const 2).aestronglyMeasurable
      (((hBm 0).sub_const _).pow_const 2).aestronglyMeasurable
  have h1 := tendstoInDistribution_clt hindep hident hφW_meas hWL2
  rw [hmeanW, hvarW] at h1
  exact h1

/-- **The oracle statistic is asymptotically `χ²₁`.** With the means `μ_A, μ_B` and variances
`Var A, Var B` known instead of fitted, `(N^{-1/2} ∑ (A - μ_A)(B - μ_B))² / (Var A · Var B)`
converges in distribution to `χ²₁`: the same limit as the fitted statistic of
`tendstoInDistribution_mul_sampleCorrSq`, so fitting the nuisance parameters costs the trend
contrast no degree of freedom. -/
theorem tendstoInDistribution_oracleStat (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P)
    (hnull : IndepFun (fun ω ↦ (X 0 ω).1) (fun ω ↦ (X 0 ω).2) P)
    (hA : MemLp (fun ω ↦ (X 0 ω).1) 2 P) (hB : MemLp (fun ω ↦ (X 0 ω).2) 2 P)
    (hvA : 0 < Var[fun ω ↦ (X 0 ω).1; P]) (hvB : 0 < Var[fun ω ↦ (X 0 ω).2; P])
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ ((√N)⁻¹ * ∑ m ∈ range N,
        ((X m ω).1 - ∫ ω, (X 0 ω).1 ∂P) * ((X m ω).2 - ∫ ω, (X 0 ω).2 ∂P)) ^ 2 /
          (Var[fun ω ↦ (X 0 ω).1; P] * Var[fun ω ↦ (X 0 ω).2; P]))
      atTop Z (fun _ ↦ P) P' := by
  set c := Var[fun ω ↦ (X 0 ω).1; P] * Var[fun ω ↦ (X 0 ω).2; P] with hc
  have hc0 : 0 < c := mul_pos hvA hvB
  have h := (tendstoInDistribution_centered hindep hident hnull hA hB).continuous_comp
    (g := fun x : ℝ ↦ x ^ 2 / c) (by fun_prop)
  refine tendstoInDistribution_of_hasLaw (Y := fun x : ℝ ↦ x ^ 2)
    (h.congr (fun N ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun x ↦ ?_))
    ⟨by fun_prop, gaussianReal_map_sq⟩ hZ
  · simp
  · simp only [Function.comp_apply]
    rw [mul_pow, Real.sq_sqrt hc0.le]
    field_simp

/-- **`N r² → χ²₁` under independence.** Let `X m = (A m, B m)` be i.i.d. pairs of real random
variables with `A 0 ⟂ B 0`, both square integrable with positive variance. Then `N` times the
squared sample correlation of the first `N` pairs converges in distribution to `χ²₁`. -/
theorem tendstoInDistribution_mul_sampleCorrSq (hindep : iIndepFun X P)
    (hident : ∀ m, IdentDistrib (X m) (X 0) P P)
    (hnull : IndepFun (fun ω ↦ (X 0 ω).1) (fun ω ↦ (X 0 ω).2) P)
    (hA : MemLp (fun ω ↦ (X 0 ω).1) 2 P) (hB : MemLp (fun ω ↦ (X 0 ω).2) 2 P)
    (hvA : 0 < Var[fun ω ↦ (X 0 ω).1; P]) (hvB : 0 < Var[fun ω ↦ (X 0 ω).2; P])
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun N ω ↦ N * sampleCorrSq (fun m ↦ (X m ω).1) (fun m ↦ (X m ω).2) N)
      atTop Z (fun _ ↦ P) P' := by
  set μA := ∫ ω, (X 0 ω).1 ∂P with hμA
  set μB := ∫ ω, (X 0 ω).2 ∂P with hμB
  set vA := Var[fun ω ↦ (X 0 ω).1; P] with hvA_def
  set vB := Var[fun ω ↦ (X 0 ω).2; P] with hvB_def
  have hXm : ∀ m, AEMeasurable (X m) P := fun m ↦ (hident m).aemeasurable_fst
  have hAm : ∀ m, AEMeasurable (fun ω ↦ (X m ω).1) P := fun m ↦ (hXm m).fst
  have hBm : ∀ m, AEMeasurable (fun ω ↦ (X m ω).2) P := fun m ↦ (hXm m).snd
  -- Step 1: the oracle numerator is asymptotically `N(0, vA vB)`.
  have h1 := tendstoInDistribution_centered hindep hident hnull hA hB
  -- Step 2: the correction `N^{-1/2} (∑ A - N μA) (μB - B̄)` tends to `0` in probability.
  have hAclt := tendstoInDistribution_clt hindep hident (φ := Prod.fst) measurable_fst hA
  have hBbar : TendstoInMeasure P (fun N ω ↦ μB - sampleMean (fun m ↦ (X m ω).2) N) atTop
      (fun _ ↦ 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun N ↦ ?_) ?_
    · refine (aemeasurable_const.sub ?_).aestronglyMeasurable
      exact (Finset.aemeasurable_fun_sum _ fun m _ ↦ hBm m).div_const _
    · filter_upwards [ae_tendsto_sampleMean hindep hident (φ := Prod.snd) measurable_snd
        (hB.integrable one_le_two)] with ω hω
      have := (tendsto_const_nhds (x := μB)).sub hω
      rwa [← hμB, sub_self] at this
  have h2 : TendstoInMeasure P
      (fun (N : ℕ) ω ↦ ((√N)⁻¹ * (∑ m ∈ range N, (X m ω).1 - N * μA)) *
        (μB - sampleMean (fun m ↦ (X m ω).2) N)) atTop (fun _ ↦ 0) := by
    have hprod := hAclt.mul_of_tendstoInMeasure_const hBbar fun N ↦
      aemeasurable_const.sub ((Finset.aemeasurable_fun_sum _ fun m _ ↦ hBm m).div_const _)
    refine tendstoInMeasure_of_tendstoInDistribution_const (P' := gaussianReal 0 1) ?_
    exact hprod.congr (fun _ ↦ ae_of_all _ fun _ ↦ rfl) (ae_of_all _ fun _ ↦ zero_mul _)
  -- Step 3: the scaled sample covariance is asymptotically `N(0, vA vB)`.
  have h3 : TendstoInDistribution
      (fun (N : ℕ) ω ↦ √N * (sampleMean (fun m ↦ (X m ω).1 * (X m ω).2) N -
        sampleMean (fun m ↦ (X m ω).2) N * sampleMean (fun m ↦ (X m ω).1) N))
      atTop (fun x : ℝ ↦ √(vA * vB) * x) (fun _ ↦ P) (gaussianReal 0 1) := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ h1 ?_ fun N ↦ ?_
    · convert h2 using 1
      funext N ω
      simp only [Pi.sub_apply]
      rw [sqrt_mul_cov_eq (fun m ↦ (X m ω).1) (fun m ↦ (X m ω).2) μA μB N]
      ring
    · refine aemeasurable_const.mul ?_
      refine AEMeasurable.sub ?_ ?_
      · exact (Finset.aemeasurable_fun_sum _ fun m _ ↦ (hAm m).mul (hBm m)).div_const _
      · exact ((Finset.aemeasurable_fun_sum _ fun m _ ↦ hBm m).div_const _).mul
          ((Finset.aemeasurable_fun_sum _ fun m _ ↦ hAm m).div_const _)
  -- Step 4: the product of the sample variances tends to `vB vA` in probability.
  have hmeas : ∀ f : ℝ × ℝ → ℝ, Measurable f → ∀ N, AEMeasurable
      (fun ω ↦ sampleMean (fun m ↦ f (X m ω)) N) P := fun f hf N ↦
    (Finset.aemeasurable_fun_sum _ fun m _ ↦ hf.comp_aemeasurable (hXm m)).div_const _
  have hDmeas : ∀ N, AEMeasurable (fun ω ↦
      (sampleMean (fun m ↦ (X m ω).2 ^ 2) N - sampleMean (fun m ↦ (X m ω).2) N ^ 2) *
        (sampleMean (fun m ↦ (X m ω).1 ^ 2) N - sampleMean (fun m ↦ (X m ω).1) N ^ 2)) P :=
    fun N ↦ ((hmeas (fun x ↦ x.2 ^ 2) (by fun_prop) N).sub
      ((hmeas Prod.snd measurable_snd N).pow_const 2)).mul
      ((hmeas (fun x ↦ x.1 ^ 2) (by fun_prop) N).sub
      ((hmeas Prod.fst measurable_fst N).pow_const 2))
  have hD : TendstoInMeasure P
      (fun N ω ↦ (sampleMean (fun m ↦ (X m ω).2 ^ 2) N - sampleMean (fun m ↦ (X m ω).2) N ^ 2) *
        (sampleMean (fun m ↦ (X m ω).1 ^ 2) N - sampleMean (fun m ↦ (X m ω).1) N ^ 2))
      atTop (fun _ ↦ vB * vA) := by
    refine tendstoInMeasure_of_tendsto_ae (fun N ↦ (hDmeas N).aestronglyMeasurable) ?_
    · filter_upwards [ae_tendsto_sampleMean hindep hident (φ := fun x ↦ x.2 ^ 2) (by fun_prop)
          hB.integrable_sq,
        ae_tendsto_sampleMean hindep hident (φ := Prod.snd) measurable_snd
          (hB.integrable one_le_two),
        ae_tendsto_sampleMean hindep hident (φ := fun x ↦ x.1 ^ 2) (by fun_prop)
          hA.integrable_sq,
        ae_tendsto_sampleMean hindep hident (φ := Prod.fst) measurable_fst
          (hA.integrable one_le_two)] with ω hB2 hB1 hA2 hA1
      have hvA' : vA = ∫ ω, (X 0 ω).1 ^ 2 ∂P - μA ^ 2 := variance_eq_sub hA
      have hvB' : vB = ∫ ω, (X 0 ω).2 ^ 2 ∂P - μB ^ 2 := variance_eq_sub hB
      rw [hvA', hvB']
      exact (hB2.sub (hB1.pow 2)).mul (hA2.sub (hA1.pow 2))
  -- Step 5: Slutsky, then identify the limit law.
  have hc : vB * vA ≠ 0 := (mul_pos hvB hvA).ne'
  have h5 := h3.continuous_comp (g := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    |>.div_of_tendstoInMeasure_const hc hD hDmeas
  refine tendstoInDistribution_of_hasLaw (Y := fun x : ℝ ↦ x ^ 2)
    (h5.congr (fun N ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun x ↦ ?_))
    ⟨by fun_prop, gaussianReal_map_sq⟩ hZ
  · simp only [sampleCorrSq, Function.comp_apply]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), mul_div_assoc]
  · simp only [Function.comp_apply]
    rw [mul_pow, Real.sq_sqrt (mul_pos hvA hvB).le]
    field_simp

end Asymptotics

/-! ### The genotype table of a sample -/

section Table

variable {Ω : Type*}

/-- The additive genotype score: the number `0, 1, 2` of copies of the counted allele. -/
def score (g : Fin 3) : ℝ := ((g : ℕ) : ℝ)

/-- The case indicator: `1` for a case, `0` for a control. -/
def caseInd (y : Bool) : ℝ := if y then 1 else 0

@[simp]
theorem caseInd_sq (y : Bool) : caseInd y ^ 2 = caseInd y := by
  cases y <;> simp [caseInd]

/-- The number of cases with genotype class `i` among the first `N` subjects, where subject `m`
has genotype class `(S m ω).1` and case status `(S m ω).2`. -/
noncomputable def caseCount (S : ℕ → Ω → Fin 3 × Bool) (N : ℕ) (ω : Ω) (i : Fin 3) : ℝ :=
  ((range N).filter fun m ↦ (S m ω).1 = i ∧ (S m ω).2 = true).card

/-- The number of controls with genotype class `i` among the first `N` subjects. -/
noncomputable def controlCount (S : ℕ → Ω → Fin 3 × Bool) (N : ℕ) (ω : Ω) (i : Fin 3) : ℝ :=
  ((range N).filter fun m ↦ (S m ω).1 = i ∧ (S m ω).2 = false).card

/-- The **Cochran–Armitage trend statistic** of the `2 × 3` table of the first `N` subjects:
`GenomicPrediction.ArmitageTrend.trendStat` of the case and control genotype counts. -/
noncomputable def caStat (S : ℕ → Ω → Fin 3 × Bool) (N : ℕ) (ω : Ω) : ℝ :=
  ArmitageTrend.trendStat (caseCount S N ω) (controlCount S N ω)

variable (S : ℕ → Ω → Fin 3 × Bool) (N : ℕ) (ω : Ω)

private theorem sum_mul_caseCount (f : Fin 3 → ℝ) :
    ∑ i, f i * caseCount S N ω i = ∑ m ∈ range N, f (S m ω).1 * caseInd (S m ω).2 := by
  simp only [caseCount, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m _ ↦ ?_
  cases (S m ω).2 <;> simp [caseInd]

private theorem sum_mul_controlCount (f : Fin 3 → ℝ) :
    ∑ i, f i * controlCount S N ω i =
      ∑ m ∈ range N, f (S m ω).1 * (1 - caseInd (S m ω).2) := by
  simp only [controlCount, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m _ ↦ ?_
  cases (S m ω).2 <;> simp [caseInd]

private theorem sum_mul_count (f : Fin 3 → ℝ) :
    ∑ i, f i * (caseCount S N ω i + controlCount S N ω i) = ∑ m ∈ range N, f (S m ω).1 := by
  simp only [mul_add, sum_add_distrib, sum_mul_caseCount, sum_mul_controlCount]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun m _ ↦ by ring

/-- **The Cochran–Armitage statistic is `N r²`** for the sample: `caStat S N ω` is `N` times the
squared sample correlation of genotype score and case indicator over the first `N` subjects. -/
theorem caStat_eq_mul_sampleCorrSq :
    caStat S N ω = N * sampleCorrSq (fun m ↦ score (S m ω).1) (fun m ↦ caseInd (S m ω).2) N := by
  have hT : ArmitageTrend.total (caseCount S N ω) (controlCount S N ω) = N := by
    simpa [ArmitageTrend.total] using sum_mul_count S N ω (fun _ ↦ 1)
  have hR : ∑ i, caseCount S N ω i = ∑ m ∈ range N, caseInd (S m ω).2 := by
    simpa using sum_mul_caseCount S N ω (fun _ ↦ 1)
  have hA : ∑ i : Fin 3, ((i : ℕ) : ℝ) * caseCount S N ω i =
      ∑ m ∈ range N, score (S m ω).1 * caseInd (S m ω).2 :=
    sum_mul_caseCount S N ω _
  have hn1 : ∑ i : Fin 3, ((i : ℕ) : ℝ) * (caseCount S N ω i + controlCount S N ω i) =
      ∑ m ∈ range N, score (S m ω).1 :=
    sum_mul_count S N ω _
  have hn2 : ∑ i : Fin 3, ((i : ℕ) : ℝ) ^ 2 * (caseCount S N ω i + controlCount S N ω i) =
      ∑ m ∈ range N, score (S m ω).1 ^ 2 :=
    sum_mul_count S N ω (fun i ↦ ((i : ℕ) : ℝ) ^ 2)
  rw [caStat, ArmitageTrend.trendStat_eq_total_mul_corrSq, hT]
  congr 1
  simp only [ArmitageTrend.corrSq, ArmitageTrend.scoreVar, sampleCorrSq, sampleMean, hT, hR, hA,
    hn1, hn2, caseInd_sq]

/-! ### Boundary cases of the finite statistic -/

/-- **No cases**: a table without cases has trend statistic `0` (the factor `R` of the
denominator vanishes). -/
theorem trendStat_eq_zero_of_no_cases (r s : Fin 3 → ℝ) (hR : ∑ i, r i = 0) :
    ArmitageTrend.trendStat r s = 0 := by
  simp [ArmitageTrend.trendStat, hR]

/-- **No controls**: a table without controls has trend statistic `0`. -/
theorem trendStat_eq_zero_of_no_controls (r s : Fin 3 → ℝ) (hS : ∑ i, s i = 0) :
    ArmitageTrend.trendStat r s = 0 := by
  simp [ArmitageTrend.trendStat, hS]

/-- **Singular design**: if every individual has the same genotype class `g`, the score has zero
sample variance, the variance factor `N ∑ i² n_i - (∑ i n_i)²` of the denominator vanishes, and
the trend statistic is `0`. -/
theorem trendStat_eq_zero_of_single_genotype (r s : Fin 3 → ℝ) (g : Fin 3)
    (hr : ∀ i, i ≠ g → r i = 0) (hs : ∀ i, i ≠ g → s i = 0) :
    ArmitageTrend.trendStat r s = 0 := by
  have hden : ArmitageTrend.total r s * ∑ i : Fin 3, ((i : ℕ) : ℝ) ^ 2 * (r i + s i) -
      (∑ i : Fin 3, ((i : ℕ) : ℝ) * (r i + s i)) ^ 2 = 0 := by
    simp only [ArmitageTrend.total, Fin.sum_univ_three]
    fin_cases g <;> simp_all <;> ring
  simp [ArmitageTrend.trendStat, hden]

end Table

/-! ### The asymptotic trend test -/

section Test

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {S : ℕ → Ω → Fin 3 × Bool}

/-- The real pair (genotype score, case indicator) of a subject. -/
private def toReal (x : Fin 3 × Bool) : ℝ × ℝ := (score x.1, caseInd x.2)

private theorem measurable_toReal : Measurable toReal := measurable_of_countable _

/-- The variance of the case indicator is `p (1 - p)` for `p = P(case)`. -/
private theorem variance_caseInd (hS0 : Measurable (S 0)) :
    Var[fun ω ↦ caseInd (S 0 ω).2; P] =
      P.real {ω | (S 0 ω).2 = true} * (1 - P.real {ω | (S 0 ω).2 = true}) := by
  have hset : MeasurableSet {ω | (S 0 ω).2 = true} :=
    (measurable_snd.comp hS0) (measurableSet_singleton true)
  have hind : (fun ω ↦ caseInd (S 0 ω).2) = {ω | (S 0 ω).2 = true}.indicator 1 := by
    funext ω
    by_cases h : (S 0 ω).2 = true <;> simp [caseInd, h]
  have hmean : ∫ ω, caseInd (S 0 ω).2 ∂P = P.real {ω | (S 0 ω).2 = true} := by
    rw [hind, integral_indicator_one hset]
  have hL2 : MemLp (fun ω ↦ caseInd (S 0 ω).2) 2 P := by
    rw [hind]
    exact (memLp_const 1).indicator hset.nullMeasurableSet
  rw [variance_eq_sub hL2]
  have hsq : (fun ω ↦ caseInd (S 0 ω).2) ^ 2 = fun ω ↦ caseInd (S 0 ω).2 := by
    funext ω
    simp
  rw [hsq, hmean]
  ring

private theorem memLp_score (hS0 : Measurable (S 0)) :
    MemLp (fun ω ↦ (toReal (S 0 ω)).1) 2 P := by
  refine memLp_of_bounded (a := 0) (b := 2) (ae_of_all _ fun ω ↦ ?_)
    ((measurable_of_countable score).comp (measurable_fst.comp hS0)).aestronglyMeasurable 2
  simp only [Function.comp_apply, score, Set.mem_Icc]
  have := (S 0 ω).1.isLt
  constructor
  · positivity
  · exact_mod_cast Nat.le_of_lt_succ this

private theorem memLp_caseInd (hS0 : Measurable (S 0)) :
    MemLp (fun ω ↦ (toReal (S 0 ω)).2) 2 P := by
  refine memLp_of_bounded (a := 0) (b := 1) (ae_of_all _ fun ω ↦ ?_)
    ((measurable_of_countable caseInd).comp (measurable_snd.comp hS0)).aestronglyMeasurable 2
  simp only [Function.comp_apply, caseInd, Set.mem_Icc]
  split_ifs <;> norm_num

/-- **The Cochran–Armitage trend test is asymptotically `χ²₁`.** Subjects `S m = (G m, Y m)`
(genotype class, case status) are i.i.d. (*multinomial sampling* of the `2 × 3` table). Under
the null `G 0 ⟂ Y 0`, with case probability `p = P(Y 0 = true) ∈ (0, 1)` and positive genotype
score variance (at least two genotype classes of positive probability), the trend statistic of
the first `N` subjects converges in distribution, as `N → ∞`, to `χ²₁`.

All three null parameters (`p` and two genotype frequencies) are fitted from the data inside
`caStat`; the limit still has one degree of freedom. -/
theorem tendstoInDistribution_caStat (hS0 : Measurable (S 0)) (hindep : iIndepFun S P)
    (hident : ∀ m, IdentDistrib (S m) (S 0) P P)
    (hnull : IndepFun (fun ω ↦ (S 0 ω).1) (fun ω ↦ (S 0 ω).2) P)
    (hp0 : 0 < P.real {ω | (S 0 ω).2 = true}) (hp1 : P.real {ω | (S 0 ω).2 = true} < 1)
    (hscore : 0 < Var[fun ω ↦ score (S 0 ω).1; P])
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution (caStat S) atTop Z (fun _ ↦ P) P' := by
  have hmain := tendstoInDistribution_mul_sampleCorrSq (X := fun m ω ↦ toReal (S m ω))
    (hindep.comp (fun _ ↦ toReal) fun _ ↦ measurable_toReal)
    (fun m ↦ (hident m).comp measurable_toReal)
    (hnull.comp (φ := score) (ψ := caseInd) (measurable_of_countable _)
      (measurable_of_countable _))
    (memLp_score hS0) (memLp_caseInd hS0) hscore ?_ hZ
  · refine hmain.congr (fun N ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
    exact (caStat_eq_mul_sampleCorrSq S N ω).symm
  · change 0 < Var[fun ω ↦ caseInd (S 0 ω).2; P]
    rw [variance_caseInd hS0]
    exact mul_pos hp0 (by linarith)

/-- **The oracle trend statistic is asymptotically `χ²₁`.** Under the hypotheses of
`tendstoInDistribution_caStat`, with the null parameters known instead of fitted (mean score
`∑ i i π_i`, case probability `p`, score variance, and case-indicator variance `p (1 - p)`),
`(N^{-1/2} ∑_{m < N} (score G_m - E score)(Y_m - p))² / (Var score · p (1 - p))` also converges
in distribution to `χ²₁`: fitting `p` and `π` does not change the degrees of freedom. -/
theorem tendstoInDistribution_caOracleStat (hS0 : Measurable (S 0)) (hindep : iIndepFun S P)
    (hident : ∀ m, IdentDistrib (S m) (S 0) P P)
    (hnull : IndepFun (fun ω ↦ (S 0 ω).1) (fun ω ↦ (S 0 ω).2) P)
    (hp0 : 0 < P.real {ω | (S 0 ω).2 = true}) (hp1 : P.real {ω | (S 0 ω).2 = true} < 1)
    (hscore : 0 < Var[fun ω ↦ score (S 0 ω).1; P])
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    TendstoInDistribution
      (fun (N : ℕ) ω ↦ ((√N)⁻¹ * ∑ m ∈ range N,
        (score (S m ω).1 - ∫ ω, score (S 0 ω).1 ∂P) *
          (caseInd (S m ω).2 - ∫ ω, caseInd (S 0 ω).2 ∂P)) ^ 2 /
          (Var[fun ω ↦ score (S 0 ω).1; P] * Var[fun ω ↦ caseInd (S 0 ω).2; P]))
      atTop Z (fun _ ↦ P) P' := by
  have hcase : 0 < Var[fun ω ↦ caseInd (S 0 ω).2; P] := by
    rw [variance_caseInd hS0]
    exact mul_pos hp0 (by linarith)
  exact tendstoInDistribution_oracleStat (X := fun m ω ↦ toReal (S m ω))
    (hindep.comp (fun _ ↦ toReal) fun _ ↦ measurable_toReal)
    (fun m ↦ (hident m).comp measurable_toReal)
    (hnull.comp (φ := score) (ψ := caseInd) (measurable_of_countable _)
      (measurable_of_countable _))
    (memLp_score hS0) (memLp_caseInd hS0) hscore hcase hZ

omit [IsProbabilityMeasure P] in
/-- **Singular design, almost surely**: if every subject almost surely has the genotype class
`g` (zero score variance), then almost surely the trend statistic is `0` for every sample
size. -/
theorem caStat_ae_eq_zero_of_genotype_const
    (hident : ∀ m, IdentDistrib (S m) (S 0) P P) {g : Fin 3}
    (hg : ∀ᵐ ω ∂P, (S 0 ω).1 = g) :
    ∀ᵐ ω ∂P, ∀ N, caStat S N ω = 0 := by
  have hall : ∀ᵐ ω ∂P, ∀ m, (S m ω).1 = g := by
    refine ae_all_iff.2 fun m ↦ ?_
    have hset : MeasurableSet {x : Fin 3 × Bool | x.1 = g} :=
      measurable_fst (measurableSet_singleton g)
    exact (hident m).symm.ae_snd (p := fun x ↦ x.1 = g) hset hg
  filter_upwards [hall] with ω hω N
  refine trendStat_eq_zero_of_single_genotype _ _ g (fun i hi ↦ ?_) fun i hi ↦ ?_ <;>
  · simp only [caseCount, controlCount, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
    intro m _ h
    exact hi (h.1 ▸ hω m)

/-- `χ²₁` has no atom at `0`. -/
private theorem chiSquareMeasure_one_singleton_zero : chiSquareMeasure 1 {0} = 0 := by
  rw [chiSquareMeasure, gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
  exact setLIntegral_measure_zero _ _ (Real.volume_singleton)

/-- **The singular design has no `χ²₁` limit**: if the genotype is almost surely a single class,
the trend statistic converges in distribution to the Dirac mass at `0`, so it does not converge
to `χ²₁`. The positive score variance hypothesis of `tendstoInDistribution_caStat` cannot be
dropped. -/
theorem not_tendstoInDistribution_caStat_of_genotype_const
    (hident : ∀ m, IdentDistrib (S m) (S 0) P P) {g : Fin 3}
    (hg : ∀ᵐ ω ∂P, (S 0 ω).1 = g)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquareMeasure 1) P') :
    ¬ TendstoInDistribution (caStat S) atTop Z (fun _ ↦ P) P' := by
  intro h
  have h0 := caStat_ae_eq_zero_of_genotype_const hident hg
  have hconst : TendstoInDistribution (caStat S) atTop (fun _ : Ω ↦ (0 : ℝ)) (fun _ ↦ P) P :=
    (tendstoInDistribution_const (Z := fun _ : Ω ↦ (0 : ℝ)) (l := atTop)
      aemeasurable_const).congr
      (fun N ↦ by filter_upwards [h0] with ω hω using (hω N).symm) (ae_of_all _ fun _ ↦ rfl)
  have huniq := tendstoInDistribution_unique _ h hconst
  rw [hZ.map_eq, Measure.map_const, measure_univ, one_smul] at huniq
  have := congrArg (fun μ : Measure ℝ ↦ μ {0}) huniq
  simp only [chiSquareMeasure_one_singleton_zero] at this
  simp at this

end Test

end MathlibExt.Biology.StatisticalGenetics.CochranArmitage

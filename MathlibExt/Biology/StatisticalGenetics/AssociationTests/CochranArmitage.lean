/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.GenomicPrediction
public import MathlibExt.Probability.Statistics.SampleCorrelation
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
The generic `N r² → χ²₁` asymptotics are proved in
`MathlibExt.Probability.Statistics.SampleCorrelation` (`tendstoInDistribution_mul_sampleCorrSq`,
`tendstoInDistribution_oracleStat`); this file specializes them to genotype tables.

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
open MathlibExt.Probability.Statistics.SampleCorrelation

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
in distribution to `χ²₁`, the same limit as the fitted statistic of
`tendstoInDistribution_caStat`. -/
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

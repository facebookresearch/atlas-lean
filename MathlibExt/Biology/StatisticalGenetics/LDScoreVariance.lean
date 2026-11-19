/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
public import MathlibExt.Probability.FiniteProbability
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# LD-score regression: the variance of the heritability estimator vanishes

Bulik-Sullivan et al. (2015) estimate SNP heritability by `ĥ² = b̂ · M / N`, where `b̂` is the
least-squares slope of the association statistics `χ²_j` of `M` markers on their LD scores
`ℓ_j` and `N` is the sample size. This file derives `Var(ĥ²) → 0` as `M → ∞` with bounded LD.

## Source receipt

* Source: Bulik-Sullivan et al. (2015), the LD-score regression estimator and its consistency
  as the number of markers grows (the paper's standard errors use a block jackknife over
  contiguous LD blocks, which is the block-dependence model below).
* Built on (merged): `LDScore.Model`, `LDScore.ldScore` (`LDScore.lean`);
  `LDScoreInflation.chiSqStrat` (`LDScoreInflation.lean`); `FiniteProbability.olsSlope`,
  `sxy`, `sampleMean`, `sum_sub_sampleMean`, `sxy_eq_sum_sub_mul` (`FiniteProbability.lean`);
  Mathlib's `covariance_fun_sum_fun_sum`, `covariance_self`, `IndepFun.covariance_eq_zero`.
* Taken as a hypothesis (open PR, T147, `LDScoreRegression.lean`, not imported): the estimator
  `h2Hat N M ℓ χ = olsSlope ℓ χ * M / N`. Every statement here takes a random variable `est`
  together with `hest : ∀ ω, est ω = olsSlope ℓ (fun j => χ j ω) * M / N`; once T147 is merged,
  `est := fun ω => h2Hat N M ℓ fun j => χ j ω` and `hest := fun _ => rfl`. The evariance limit
  `tendsto_evariance_h2Hat_chiSqStrat` is then exactly the `hvar` hypothesis of T147's
  consistency theorem `tendstoInMeasure_h2Hat`.
* Proved here: everything else.

## Why a model extension is needed

`LDScore.Model` fixes only second moments of effects and noise, so the covariances of the
statistics `χ²_j = N β̂_j²` (fourth moments of the data) are not determined by it. This file adds
the missing fourth-moment / dependence structure explicitly:

* **Fourth moments:** `χ²_j ∈ L²` with `Var(χ²_j) ≤ V`. Under Gaussian scores
  `Var(χ²_j) = 2 (𝔼 χ²_j)² - 2 (N a)² ≤ 2 (𝔼 χ²_j)²` with
  `𝔼 χ²_j = 1 + N h² ℓ_j / M + N a - h²`, so a uniform `V` corresponds to bounded LD scores
  `ℓ_j` with `N / M` and `N a` bounded.
* **Bounded LD (dependence):** the markers are partitioned into LD blocks of size at most `K`,
  and statistics in different blocks are independent (`LDBlockModel`). Under Gaussian scores
  with a block-diagonal sample LD matrix the scores of different blocks are uncorrelated and
  jointly Gaussian, hence independent.

## Main results

* `sum_mul_mul_le_of_rowSum`: for a symmetric matrix `C` whose absolute row sums are at most
  `R`, `∑ j k, w j w k C j k ≤ R ∑ j, w j ^ 2`.
* `variance_olsSlope_le`: if the absolute covariance row sums of the responses are at most `R`,
  then `Var(b̂) ≤ R / S_ℓℓ`.
* `variance_h2Hat_le`: `Var(ĥ²) ≤ (M / N)² R / S_ℓℓ`.
* `LDBlockModel.sum_abs_covariance_le`: under the block model the row sums are at most `K V`.
* `tendsto_variance_h2Hat_of_rowSum`: along designs with uniformly bounded row sums,
  LD-score spread `S_ℓℓ ≥ c M` (`c > 0`), and `M / N² → 0`, `Var(ĥ²) → 0`.
* `tendsto_variance_h2Hat_of_ldBlock`: the same under the block model with `M → ∞` and
  `N ≥ κ M` (`κ > 0`).
* `tendsto_evariance_h2Hat_chiSqStrat`: the LD-score regression case, with the statistics
  `chiSqStrat` of the merged model, in the `evariance` form of T147's `hvar`.

## Assumptions, stated

The LD-score spread condition `S_ℓℓ = ∑ j, (ℓ_j - ℓ̄)² ≥ c M` says the sample variance of the
LD scores stays bounded away from `0`; without it the slope is not identified in the limit.
The paper fits by weighted least squares; this file treats the unweighted fit, as T147 does.

## References

* B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working
  Group of the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price,
  B. M. Neale, *LD Score regression distinguishes confounding from polygenicity in
  genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Probability.FiniteProbability

namespace MathlibExt.Biology.StatisticalGenetics.LDScoreVariance

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### A quadratic-form bound from row sums -/

/-- **Row-sum bound for a quadratic form.** If `C` is symmetric and every absolute row sum
`∑ k, |C j k|` is at most `R`, then `∑ j k, w j * w k * C j k ≤ R * ∑ j, w j ^ 2`. -/
theorem sum_mul_mul_le_of_rowSum {ι : Type*} [Fintype ι] (C : ι → ι → ℝ)
    (hC : ∀ j k, C j k = C k j) {R : ℝ} (hR : ∀ j, ∑ k, |C j k| ≤ R) (w : ι → ℝ) :
    ∑ j, ∑ k, w j * w k * C j k ≤ R * ∑ j, w j ^ 2 := by
  have hterm : ∀ j k, w j * w k * C j k ≤
      w j ^ 2 / 2 * |C j k| + w k ^ 2 / 2 * |C k j| := by
    intro j k
    rw [← hC j k]
    have h1 : w j * w k * C j k ≤ |w j| * |w k| * |C j k| := by
      rw [← abs_mul, ← abs_mul]
      exact le_abs_self _
    have h2 : |w j| * |w k| ≤ w j ^ 2 / 2 + w k ^ 2 / 2 := by
      nlinarith [sq_nonneg (|w j| - |w k|), sq_abs (w j), sq_abs (w k)]
    nlinarith [abs_nonneg (C j k)]
  have hhalf : ∀ j, ∑ k, w j ^ 2 / 2 * |C j k| ≤ w j ^ 2 / 2 * R := fun j => by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (hR j) (by positivity)
  calc ∑ j, ∑ k, w j * w k * C j k
      ≤ ∑ j, ∑ k, (w j ^ 2 / 2 * |C j k| + w k ^ 2 / 2 * |C k j|) :=
        sum_le_sum fun j _ => sum_le_sum fun k _ => hterm j k
    _ = ∑ j, ∑ k, w j ^ 2 / 2 * |C j k| + ∑ k, ∑ j, w k ^ 2 / 2 * |C k j| := by
        simp only [sum_add_distrib]
        congr 1
        exact sum_comm
    _ ≤ ∑ j, w j ^ 2 / 2 * R + ∑ k, w k ^ 2 / 2 * R :=
        add_le_add (sum_le_sum fun j _ => hhalf j) (sum_le_sum fun k _ => hhalf k)
    _ = R * ∑ j, w j ^ 2 := by
        rw [← sum_add_distrib, mul_sum]
        exact sum_congr rfl fun j _ => by ring

/-! ### The variance of a linear combination -/

/-- The variance of a linear combination `∑ j, a j * Y j` of square-integrable random variables
is the quadratic form `∑ j k, a j * a k * Cov(Y j, Y k)`. -/
theorem variance_fun_sum_mul_eq [IsFiniteMeasure μ] {ι : Type*} [Fintype ι] (a : ι → ℝ)
    {Y : ι → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) :
    Var[fun ω => ∑ j, a j * Y j ω; μ] = ∑ j, ∑ k, a j * a k * cov[Y j, Y k; μ] := by
  have hY' : ∀ j, MemLp (fun ω => a j * Y j ω) 2 μ := fun j => (hY j).const_mul (a j)
  have hsum : MemLp (fun ω => ∑ j, a j * Y j ω) 2 μ := memLp_finsetSum univ fun j _ => hY' j
  rw [← covariance_self hsum.aestronglyMeasurable.aemeasurable,
    covariance_fun_sum_fun_sum hY' hY']
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- **Variance of a linear combination under a covariance row-sum bound.** If every absolute
covariance row sum `∑ k, |Cov(Y j, Y k)|` is at most `R`, then
`Var(∑ j, a j * Y j) ≤ R * ∑ j, a j ^ 2`. -/
theorem variance_fun_sum_mul_le [IsFiniteMeasure μ] {ι : Type*} [Fintype ι] (a : ι → ℝ)
    {Y : ι → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) {R : ℝ}
    (hR : ∀ j, ∑ k, |cov[Y j, Y k; μ]| ≤ R) :
    Var[fun ω => ∑ j, a j * Y j ω; μ] ≤ R * ∑ j, a j ^ 2 := by
  rw [variance_fun_sum_mul_eq a hY]
  exact sum_mul_mul_le_of_rowSum (fun j k => cov[Y j, Y k; μ])
    (fun j k => covariance_comm (Y j) (Y k)) hR a

/-! ### The least-squares slope as a linear combination -/

/-- The least-squares slope is the linear combination
`b̂ = ∑ j, ((x j - x̄) / S_xx) * y j` of the responses. -/
theorem olsSlope_eq_sum {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    olsSlope x y = ∑ j, (x j - sampleMean x) / sxy x x * y j := by
  rw [olsSlope, sxy_eq_sum_sub_mul, sum_div]
  exact sum_congr rfl fun j _ => by ring

/-- The squared weights of the least-squares slope sum to `1 / S_xx` (both sides are `0` when
`S_xx = 0`). -/
theorem sum_olsWeight_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ∑ j, ((x j - sampleMean x) / sxy x x) ^ 2 = 1 / sxy x x := by
  have hS : sxy x x = ∑ j, (x j - sampleMean x) ^ 2 := by
    rw [sxy]
    exact sum_congr rfl fun j _ => by ring
  simp only [div_pow]
  rw [← sum_div, ← hS]
  by_cases h : sxy x x = 0
  · simp [h]
  · field_simp

/-- **Variance of the least-squares slope.** If the responses are square integrable and every
absolute covariance row sum is at most `R`, then `Var(b̂) ≤ R / S_xx`. -/
theorem variance_olsSlope_le [IsFiniteMeasure μ] {ι : Type*} [Fintype ι] (x : ι → ℝ)
    {Y : ι → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) {R : ℝ}
    (hR : ∀ j, ∑ k, |cov[Y j, Y k; μ]| ≤ R) :
    Var[fun ω => olsSlope x fun j => Y j ω; μ] ≤ R / sxy x x := by
  simp only [olsSlope_eq_sum]
  have h := variance_fun_sum_mul_le (fun j => (x j - sampleMean x) / sxy x x) hY hR
  rwa [sum_olsWeight_sq, mul_one_div] at h

/-! ### The heritability estimator -/

/-- **Variance bound for the LD-score regression estimator.** For `est = b̂ · M / N` (T147's
`h2Hat`, passed in through `hest`) with square-integrable statistics whose absolute
covariance row sums are at most `R`, `Var(ĥ²) ≤ (M / N)² R / S_ℓℓ`. -/
theorem variance_h2Hat_le [IsFiniteMeasure μ] {N M : ℕ} (ℓ : Fin M → ℝ)
    {χ : Fin M → Ω → ℝ} (hχ : ∀ j, MemLp (χ j) 2 μ) {R : ℝ}
    (hR : ∀ j, ∑ k, |cov[χ j, χ k; μ]| ≤ R) {est : Ω → ℝ}
    (hest : ∀ ω, est ω = olsSlope ℓ (fun j => χ j ω) * M / N) :
    Var[est; μ] ≤ ((M : ℝ) / N) ^ 2 * (R / sxy ℓ ℓ) := by
  have e : est = fun ω => ((M : ℝ) / N) * olsSlope ℓ (fun j => χ j ω) := by
    funext ω
    rw [hest]
    ring
  rw [e, variance_const_mul]
  exact mul_le_mul_of_nonneg_left (variance_olsSlope_le ℓ hχ hR) (sq_nonneg _)

/-- The estimator `b̂ · M / N` of square-integrable statistics is square integrable. -/
theorem memLp_h2Hat {N M : ℕ} (ℓ : Fin M → ℝ) {χ : Fin M → Ω → ℝ}
    (hχ : ∀ j, MemLp (χ j) 2 μ) {est : Ω → ℝ}
    (hest : ∀ ω, est ω = olsSlope ℓ (fun j => χ j ω) * M / N) : MemLp est 2 μ := by
  have e : est = fun ω => ∑ j, (M : ℝ) / N * ((ℓ j - sampleMean ℓ) / sxy ℓ ℓ) * χ j ω := by
    funext ω
    rw [hest, olsSlope_eq_sum, sum_mul, sum_div]
    exact sum_congr rfl fun j _ => by ring
  rw [e]
  exact memLp_finsetSum univ fun j _ => (hχ j).const_mul _

/-! ### The LD-block model: fourth moments and bounded LD -/

/-- **LD-block dependence model** for statistics `χ : Fin M → Ω → ℝ` (the fourth-moment /
independence extension of `LDScore.Model`): the markers are partitioned into blocks of at most
`K` markers, statistics in different blocks are independent, and each statistic is square
integrable with variance at most `V`. -/
structure LDBlockModel {M : ℕ} (μ : Measure Ω) (χ : Fin M → Ω → ℝ) (K : ℕ) (V : ℝ) where
  /-- The LD block of each marker. -/
  block : Fin M → ℕ
  /-- Every LD block has at most `K` markers. -/
  card_block_le : ∀ j, #{k | block k = block j} ≤ K
  /-- Statistics of markers in different LD blocks are independent. -/
  indepFun : ∀ j k, block j ≠ block k → IndepFun (χ j) (χ k) μ
  /-- Each statistic is square integrable (finite fourth moment of the score). -/
  memLp : ∀ j, MemLp (χ j) 2 μ
  /-- Each statistic has variance at most `V`. -/
  variance_le : ∀ j, Var[χ j; μ] ≤ V

/-- `2 |Cov(X, Y)| ≤ Var X + Var Y` for square-integrable `X`, `Y`. -/
theorem two_mul_abs_covariance_le [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) : 2 * |cov[X, Y; μ]| ≤ Var[X; μ] + Var[Y; μ] := by
  have hXX := covariance_self (μ := μ) hX.aestronglyMeasurable.aemeasurable
  have hYY := covariance_self (μ := μ) hY.aestronglyMeasurable.aemeasurable
  have hYX := covariance_comm (μ := μ) Y X
  have hp : 0 ≤ Var[X + Y; μ] := variance_nonneg _ _
  have hm : 0 ≤ Var[X - Y; μ] := variance_nonneg _ _
  rw [← covariance_self (hX.add hY).aestronglyMeasurable.aemeasurable,
    covariance_add_left hX hY (hX.add hY), covariance_add_right hX hX hY,
    covariance_add_right hY hX hY] at hp
  rw [← covariance_self (hX.sub hY).aestronglyMeasurable.aemeasurable,
    covariance_sub_left hX hY (hX.sub hY), covariance_sub_right hX hX hY,
    covariance_sub_right hY hX hY] at hm
  rcases abs_cases (cov[X, Y; μ]) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

namespace LDBlockModel

variable {M K : ℕ} {V : ℝ} {χ : Fin M → Ω → ℝ}

/-- Under the LD-block model the covariance of two statistics is at most `V` in absolute
value. -/
theorem abs_covariance_le [IsFiniteMeasure μ] (B : LDBlockModel μ χ K V) (j k : Fin M) :
    |cov[χ j, χ k; μ]| ≤ V := by
  have h := two_mul_abs_covariance_le (B.memLp j) (B.memLp k)
  linarith [B.variance_le j, B.variance_le k]

/-- **Bounded LD gives bounded covariance row sums.** Under the LD-block model,
`∑ k, |Cov(χ j, χ k)| ≤ K V` for every marker `j`. -/
theorem sum_abs_covariance_le [IsFiniteMeasure μ] (B : LDBlockModel μ χ K V) (j : Fin M) :
    ∑ k, |cov[χ j, χ k; μ]| ≤ K * V := by
  have hV : 0 ≤ V := (variance_nonneg _ _).trans (B.variance_le j)
  have hzero : ∀ k, |cov[χ j, χ k; μ]| =
      if B.block k = B.block j then |cov[χ j, χ k; μ]| else 0 := fun k => by
    split_ifs with h
    · rfl
    · rw [(B.indepFun j k fun h' => h h'.symm).covariance_eq_zero (B.memLp j) (B.memLp k),
        abs_zero]
  calc ∑ k, |cov[χ j, χ k; μ]|
      = ∑ k, if B.block k = B.block j then |cov[χ j, χ k; μ]| else 0 :=
        sum_congr rfl fun k _ => hzero k
    _ ≤ ∑ k, if B.block k = B.block j then V else 0 :=
        sum_le_sum fun k _ => by split_ifs <;> simp [B.abs_covariance_le j k]
    _ = #{k | B.block k = B.block j} * V := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ K * V := mul_le_mul_of_nonneg_right (by exact_mod_cast B.card_block_le j) hV

/-- `0 ≤ V` under the LD-block model, as soon as there is a marker. -/
theorem nonneg (B : LDBlockModel μ χ K V) (j : Fin M) : 0 ≤ V :=
  (variance_nonneg _ _).trans (B.variance_le j)

end LDBlockModel

/-! ### The limit `Var(ĥ²) → 0` -/

/-- The deterministic rate: if `S ≥ c M` with `c > 0` and `0 ≤ R`, then
`(M / N)² (R / S) ≤ (R / c) (M / N²)`. -/
theorem sq_div_mul_div_le {N M : ℕ} {R S c : ℝ} (hR : 0 ≤ R) (hc : 0 < c) (hS : c * M ≤ S) :
    ((M : ℝ) / N) ^ 2 * (R / S) ≤ R / c * ((M : ℝ) / (N : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · simp [hM]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hcM : 0 < c * M := mul_pos hc hM'
  have hS' : 0 < S := hcM.trans_le hS
  have h1 : R / S ≤ R / (c * M) := div_le_div_of_nonneg_left hR hcM hS
  calc ((M : ℝ) / N) ^ 2 * (R / S) ≤ ((M : ℝ) / N) ^ 2 * (R / (c * M)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = R / c * ((M : ℝ) / (N : ℝ) ^ 2) := by
        rw [div_pow]
        field_simp

/-- **`Var(ĥ²) → 0` under bounded covariance row sums.** Along a family of designs indexed by a
filter `l`, with square-integrable statistics whose absolute covariance row sums are at most
`R` uniformly, LD-score spread `S_ℓℓ ≥ c M` with `c > 0`, and `M / N² → 0`, the variance of the
estimator `b̂ · M / N` tends to `0`. -/
theorem tendsto_variance_h2Hat_of_rowSum [IsFiniteMeasure μ] {ι : Type*} {l : Filter ι}
    {N M : ι → ℕ} (ℓ : ∀ n, Fin (M n) → ℝ) {χ : ∀ n, Fin (M n) → Ω → ℝ}
    (hχ : ∀ n j, MemLp (χ n j) 2 μ) {R : ℝ} (hR : ∀ n j, ∑ k, |cov[χ n j, χ n k; μ]| ≤ R)
    {c : ℝ} (hc : 0 < c) (hspread : ∀ n, c * M n ≤ sxy (ℓ n) (ℓ n))
    (hrate : Tendsto (fun n => (M n : ℝ) / (N n : ℝ) ^ 2) l (𝓝 0)) {est : ι → Ω → ℝ}
    (hest : ∀ n ω, est n ω = olsSlope (ℓ n) (fun j => χ n j ω) * M n / N n) :
    Tendsto (fun n => Var[est n; μ]) l (𝓝 0) := by
  set R' := max R 0
  have hR' : ∀ n j, ∑ k, |cov[χ n j, χ n k; μ]| ≤ R' := fun n j => (hR n j).trans (le_max_left _ _)
  have hbound : ∀ n, Var[est n; μ] ≤ R' / c * ((M n : ℝ) / (N n : ℝ) ^ 2) := fun n =>
    (variance_h2Hat_le (ℓ n) (hχ n) (hR' n) (hest n)).trans
      (sq_div_mul_div_le (le_max_right _ _) hc (hspread n))
  have hlim : Tendsto (fun n => R' / c * ((M n : ℝ) / (N n : ℝ) ^ 2)) l (𝓝 0) := by
    simpa using hrate.const_mul (R' / c)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => variance_nonneg _ _) hbound

/-- `M / N² → 0` when `M → ∞` and `N ≥ κ M` with `κ > 0`. -/
theorem tendsto_div_sq_of_le {ι : Type*} {l : Filter ι} {N M : ι → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hNM : ∀ n, κ * M n ≤ N n) (hM : Tendsto M l atTop) :
    Tendsto (fun n => (M n : ℝ) / (N n : ℝ) ^ 2) l (𝓝 0) := by
  have hinv : Tendsto (fun n => (κ ^ 2)⁻¹ * (M n : ℝ)⁻¹) l (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hM)).const_mul (κ ^ 2)⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
    (Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [hM.eventually_gt_atTop 0] with n hn
  have hM' : (0 : ℝ) < M n := by exact_mod_cast hn
  have hN : κ * M n ≤ N n := hNM n
  have hκM : 0 < κ * M n := mul_pos hκ hM'
  have hsq : (κ * M n) ^ 2 ≤ (N n : ℝ) ^ 2 := pow_le_pow_left₀ hκM.le hN 2
  rw [div_le_iff₀ (hκM.trans_le hN |> fun h => pow_pos h 2)]
  calc (M n : ℝ) = (κ ^ 2)⁻¹ * (M n : ℝ)⁻¹ * (κ * M n) ^ 2 := by field_simp
    _ ≤ (κ ^ 2)⁻¹ * (M n : ℝ)⁻¹ * (N n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

/-- **`Var(ĥ²) → 0` as `M → ∞` with bounded LD.** Along a family of designs with `M → ∞`,
`N ≥ κ M` (`κ > 0`), LD-score spread `S_ℓℓ ≥ c M` (`c > 0`), and statistics satisfying the
LD-block model with block size at most `K` and variance at most `V` uniformly, the variance
of the estimator `b̂ · M / N` tends to `0`. -/
theorem tendsto_variance_h2Hat_of_ldBlock [IsFiniteMeasure μ] {ι : Type*} {l : Filter ι}
    {N M : ι → ℕ} (ℓ : ∀ n, Fin (M n) → ℝ) {χ : ∀ n, Fin (M n) → Ω → ℝ} {K : ℕ} {V : ℝ}
    (B : ∀ n, LDBlockModel μ (χ n) K V) {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (hspread : ∀ n, c * M n ≤ sxy (ℓ n) (ℓ n)) (hNM : ∀ n, κ * M n ≤ N n)
    (hM : Tendsto M l atTop) {est : ι → Ω → ℝ}
    (hest : ∀ n ω, est n ω = olsSlope (ℓ n) (fun j => χ n j ω) * M n / N n) :
    Tendsto (fun n => Var[est n; μ]) l (𝓝 0) :=
  tendsto_variance_h2Hat_of_rowSum ℓ (fun n => (B n).memLp)
    (fun n j => (B n).sum_abs_covariance_le j) hc hspread (tendsto_div_sq_of_le hκ hNM hM) hest

/-! ### The LD-score regression case -/

/-- **`Var(ĥ²) → 0` for LD-score regression.** For the statistics `χ²_j = chiSqStrat` of the
merged LD-score model with stratification, along designs with `M → ∞`, `N ≥ κ M`, LD-score
spread `S_ℓℓ ≥ c M`, and the LD-block model (block size at most `K`, `Var(χ²_j) ≤ V`), the
LD-score regression estimator `ĥ² = b̂ · M / N` (T147's `h2Hat`, passed in through `hest`)
satisfies `evariance ĥ² → 0`. This is the `hvar` hypothesis of T147's consistency theorem
`tendstoInMeasure_h2Hat`. -/
theorem tendsto_evariance_h2Hat_chiSqStrat [IsFiniteMeasure μ] {ι : Type*} {l : Filter ι}
    {N M : ι → ℕ} (D : ∀ n, Model μ (N n) (M n)) (X : ∀ n, Matrix (Fin (N n)) (Fin (M n)) ℝ)
    (s : ι → ℝ) (c : ∀ n, Fin (N n) → ℝ) {K : ℕ} {V : ℝ}
    (B : ∀ n, LDBlockModel μ (chiSqStrat (D n) (X n) (s n) (c n)) K V) {c₀ κ : ℝ}
    (hc₀ : 0 < c₀) (hκ : 0 < κ) (hspread : ∀ n, c₀ * M n ≤ sxy (ldScore (X n)) (ldScore (X n)))
    (hNM : ∀ n, κ * M n ≤ N n) (hM : Tendsto M l atTop) {est : ι → Ω → ℝ}
    (hest : ∀ n ω, est n ω =
      olsSlope (ldScore (X n)) (fun j => chiSqStrat (D n) (X n) (s n) (c n) j ω) * M n / N n) :
    Tendsto (fun n => evariance (est n) μ) l (𝓝 0) := by
  have hvar := tendsto_variance_h2Hat_of_ldBlock (fun n => ldScore (X n)) B hc₀ hκ hspread hNM
    hM hest
  have e : ∀ n, evariance (est n) μ = ENNReal.ofReal (Var[est n; μ]) := fun n =>
    ((memLp_h2Hat _ (B n).memLp (hest n)).ofReal_variance_eq).symm
  simp only [e]
  simpa using ENNReal.tendsto_ofReal hvar

end MathlibExt.Biology.StatisticalGenetics.LDScoreVariance

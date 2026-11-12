/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.Probability.Statistics.Survival.CoxPartialLikelihood
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Survival inference from process-level limits

Inferential corollaries of process-level survival limits. The limits themselves are
**hypotheses** of every theorem here: each takes a scalar or finite-dimensional marginal of a
process-level limit, as a `TendstoInDistribution` statement to a centered Gaussian limit, plus
consistency
(`TendstoInMeasure`) of a variance estimator, and derives coverage or size by Slutsky's
theorem and the portmanteau theorem. The Nelson–Aalen, Kaplan–Meier and Aalen–Johansen
process limits do not by themselves give the Cox and log-rank limits used here; those are
separate hypotheses.

## Pointwise intervals versus simultaneous bands

* A **pointwise** interval targets one estimand (a Cox coefficient, or a cumulative hazard
  at one time `t`). `tendsto_coverage_waldInterval` proves that the studentized Wald
  interval has asymptotic coverage equal to the standard-normal mass of `[-z, z]`;
  `tendsto_coverage_cox_waldInterval` specializes it to the Cox Wald interval
  `βhat ± z / √(coxInformation)`, and `tendsto_logRank_rejection` gives the asymptotic size
  of the two-sided log-rank (Cox score) test.
* A **simultaneous** band must contain the whole target curve at once.
  `tendsto_coverage_gridBand` proves asymptotic simultaneous coverage on any finite grid of
  time points, with limit `P (∀ j, |Z j| ≤ z √(v j))` determined by the joint limit law.
  `gridBand_limit_le_pointwise` shows the simultaneous limit coverage never exceeds the
  pointwise coverage at any grid point, so a pointwise critical value cannot raise
  simultaneous coverage above the pointwise level; equality is possible (e.g. perfectly
  correlated coordinates). `one_sub_card_mul_le_gridBand_limit` gives the Bonferroni lower
  bound.

## Scope

Simultaneous bands are proved on finite time grids only. A band over a continuum horizon
`[0, τ]` (Hall–Wellner, equal-precision) needs weak convergence in `ℓ^∞[0, τ]` or the
Skorokhod space and a sup-norm continuous-mapping step; neither is stated here, and no
claim is made about continuum bands. Critical values (the quantile `z` with prescribed
grid coverage) are not constructed; the theorems hold for every `z`.

## Main results

* `tendsto_measureReal_preimage_of_tendstoInDistribution`: portmanteau on preimages.
* `tendsto_measureReal_abs_le_mul`: studentized Slutsky–portmanteau limit.
* `tendsto_coverage_waldInterval`, `tendsto_coverage_cox_waldInterval`: pointwise coverage.
* `tendsto_logRank_rejection`: asymptotic size of the log-rank test.
* `tendsto_coverage_gridBand`: simultaneous coverage on a finite grid.
* `gridBand_limit_le_pointwise`, `one_sub_card_mul_le_gridBand_limit`: comparison with
  pointwise coverage.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace MathlibExt.Probability.Statistics.ProcessInference

variable {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Portmanteau on preimages.** If `X n` converges in distribution to `Z` and the frontier of a
measurable set `B` is null for the law of `Z`, then `P (X n ∈ B) → P' (Z ∈ B)`. -/
theorem tendsto_measureReal_preimage_of_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    {X : ℕ → Ω → E} {Z : Ω' → E} (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P')
    {B : Set E} (hB : MeasurableSet B) (hfr : P'.map Z (frontier B) = 0) :
    Tendsto (fun n ↦ P.real (X n ⁻¹' B)) atTop (𝓝 (P'.real (Z ⁻¹' B))) := by
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto
    (E := B) (by simpa using hfr)
  simp only [ProbabilityMeasure.coe_mk] at key
  rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit hB] at key
  have key' : Tendsto (fun n ↦ P (X n ⁻¹' B)) atTop (𝓝 (P' (Z ⁻¹' B))) := by
    refine key.congr fun n ↦ ?_
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hB]
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp key'

/-! ### Pointwise Wald intervals -/

/-- The two-sided Wald interval `[est - z * se, est + z * se]` with point estimate `est`,
standard error `se` and critical value `z`. -/
def waldInterval (est se z : ℝ) : Set ℝ :=
  Set.Icc (est - z * se) (est + z * se)

theorem mem_waldInterval_iff {est se z β : ℝ} :
    β ∈ waldInterval est se z ↔ |est - β| ≤ z * se := by
  rw [waldInterval, Set.mem_Icc, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Membership of the Wald interval with standard error `s / √n` is the studentized event
`|√n (est - β)| ≤ z * s`. -/
theorem mem_waldInterval_div_sqrt_iff {est s z β : ℝ} {n : ℕ} (hn : 0 < n) :
    β ∈ waldInterval est (s / √(n : ℝ)) z ↔ |√(n : ℝ) * (est - β)| ≤ z * s := by
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [mem_waldInterval_iff, abs_mul, abs_of_pos hsq, mul_div_assoc', le_div_iff₀ hsq,
    mul_comm |est - β|]

/-- The closed studentized acceptance region `{(x, s) | |x| ≤ z * s}` in `ℝ × ℝ`. -/
private def studRegion (z : ℝ) : Set (ℝ × ℝ) := {p | |p.1| ≤ z * p.2}

private theorem measurableSet_studRegion (z : ℝ) : MeasurableSet (studRegion z) :=
  measurableSet_le (by fun_prop) (by fun_prop)

private theorem frontier_studRegion_subset (z : ℝ) :
    frontier (studRegion z) ⊆ {p : ℝ × ℝ | |p.1| = z * p.2} :=
  frontier_le_subset_eq (by fun_prop) (by fun_prop)

/-- A nondegenerate centered Gaussian puts no mass on `{|x| = c}`. -/
private theorem gaussianReal_abs_eq_null {v : NNReal} (hv : v ≠ 0) (c : ℝ) :
    gaussianReal 0 v {x | |x| = c} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  refine measure_mono_null (t := {c, -c}) ?_ ((Set.toFinite _).measure_zero _)
  intro x (hx : |x| = c)
  rcases abs_choice x with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by simp only [Set.mem_singleton_iff]; linarith)

/-- Standardizing a centered Gaussian of variance `v ≠ 0`: the mass of `{|x| ≤ z √v}` equals
the standard-normal mass of `[-z, z]`. -/
theorem gaussianReal_real_abs_le_mul_sqrt {v : NNReal} (hv : v ≠ 0) (z : ℝ) :
    (gaussianReal 0 v).real {x | |x| ≤ z * √(v : ℝ)} =
      (gaussianReal 0 1).real (Set.Icc (-z) z) := by
  have hs : 0 < √(v : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hmap : (gaussianReal 0 v).map (· / √(v : ℝ)) = gaussianReal 0 1 := by
    rw [gaussianReal_map_div_const, zero_div]
    congr 1
    ext
    simp [Real.sq_sqrt (NNReal.coe_nonneg v), hv]
  have hpre : {x : ℝ | |x| ≤ z * √(v : ℝ)} = (· / √(v : ℝ)) ⁻¹' Set.Icc (-z) z := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc]
    rw [le_div_iff₀ hs, div_le_iff₀ hs, abs_le, neg_mul]
  rw [hpre, ← map_measureReal_apply (by fun_prop) measurableSet_Icc, hmap]

/-- **Studentized Slutsky–portmanteau limit.** If `X n` converges in distribution to a
centered Gaussian of variance `v ≠ 0` and `S n` converges in probability to `√v`, then
`P (|X n| ≤ z * S n)` tends to the standard-normal mass of `[-z, z]`. -/
theorem tendsto_measureReal_abs_le_mul {X S : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    {v : NNReal} (hv : v ≠ 0) (z : ℝ)
    (hlim : TendstoInDistribution X atTop Z (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hS : TendstoInMeasure P S atTop (fun _ ↦ √(v : ℝ)))
    (hS_meas : ∀ n, AEMeasurable (S n) P) :
    Tendsto (fun n ↦ P.real {ω | |X n ω| ≤ z * S n ω}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc (-z) z))) := by
  have hpair := hlim.prodMk_of_tendstoInMeasure_const _ S Z hS hS_meas
  have hnull : P'.map (fun ω ↦ (Z ω, √(v : ℝ))) (frontier (studRegion z)) = 0 := by
    refine measure_mono_null (frontier_studRegion_subset z) ?_
    rw [Measure.map_apply_of_aemeasurable (hZ.aemeasurable.prodMk aemeasurable_const)
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))]
    have h := gaussianReal_abs_eq_null hv (z * √(v : ℝ))
    rw [← hZ.map_eq, Measure.map_apply_of_aemeasurable hZ.aemeasurable
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))] at h
    exact h
  have hport := tendsto_measureReal_preimage_of_tendstoInDistribution hpair
    (measurableSet_studRegion z) hnull
  have hlimval : P'.real ((fun ω ↦ (Z ω, √(v : ℝ))) ⁻¹' studRegion z) =
      (gaussianReal 0 1).real (Set.Icc (-z) z) := by
    rw [← gaussianReal_real_abs_le_mul_sqrt hv z]
    exact hZ.measureReal_eq (p := fun x ↦ |x| ≤ z * √(v : ℝ))
      (measurableSet_le (by fun_prop) (by fun_prop))
  rw [hlimval] at hport
  exact hport

/-- **Pointwise asymptotic coverage of a studentized Wald interval.** Suppose the centered and
`√n`-scaled estimator `√n (est n - β)` converges in distribution to a centered Gaussian of variance
`v ≠ 0` (a marginal of the process-level limit, taken as a hypothesis), and `se n` is a consistent
estimator of the asymptotic standard deviation `√v`. Then the coverage probability of the Wald
interval `waldInterval (est n) (se n / √n) z` tends to the standard-normal mass of `[-z, z]`. This
is a statement about one fixed estimand `β`; it says nothing about joint coverage of several
estimands (see `tendsto_coverage_gridBand`). -/
theorem tendsto_coverage_waldInterval {est se : ℕ → Ω → ℝ} {β : ℝ} {Z : Ω' → ℝ}
    {v : NNReal} (hv : v ≠ 0) (z : ℝ)
    (hlim : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (est n ω - β)) atTop Z
      (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hse : TendstoInMeasure P se atTop (fun _ ↦ √(v : ℝ)))
    (hse_meas : ∀ n, AEMeasurable (se n) P) :
    Tendsto (fun n : ℕ ↦ P.real {ω | β ∈ waldInterval (est n ω) (se n ω / √(n : ℝ)) z}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc (-z) z))) := by
  refine (tendsto_measureReal_abs_le_mul hv z hlim hZ hse hse_meas).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  congr 1
  ext ω
  exact (mem_waldInterval_div_sqrt_iff hn).symm

/-! ### The log-rank test -/

open MathlibExt.Probability.Statistics.CoxPartialLikelihood

/-- The two-sided log-rank test at critical value `z` rejects when the observed-minus-expected
group-1 event count exceeds `z` times the square root of its Breslow variance:
`z * √(breslowInformation T δ g) < |observedMinusExpected T δ g|`. By `coxScore_zero` and
`coxInformation_zero` this is the Cox score test of `β = 0` for the group indicator; the
Breslow variance agrees with the hypergeometric log-rank variance when event times are
distinct (see `breslowInformation`). -/
def logRankRejects {n : ℕ} (T : Fin n → ℝ) (δ : Fin n → Bool) (g : Fin n → Bool) (z : ℝ) :
    Prop :=
  z * √(breslowInformation T δ g) < |observedMinusExpected T δ g|

/-- **Asymptotic size of the log-rank test.** Take as hypotheses the null limit of the log-rank
numerator (a marginal of the process-level limit), `(O - E) / √n ⟶ N(0, v)` with `v ≠ 0`, and
consistency of the normalized Breslow variance, `√(I / n) ⟶ √v` in probability. Then the rejection
probability of the two-sided level-`z` log-rank test tends to the standard-normal mass outside
`[-z, z]`. -/
theorem tendsto_logRank_rejection {T : (n : ℕ) → Ω → Fin n → ℝ}
    {δ g : (n : ℕ) → Ω → Fin n → Bool} {Z : Ω' → ℝ} {v : NNReal} (hv : v ≠ 0) (z : ℝ)
    (hlim : TendstoInDistribution
      (fun (n : ℕ) ω ↦ observedMinusExpected (T n ω) (δ n ω) (g n ω) / √(n : ℝ)) atTop Z
      (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hinfo : TendstoInMeasure P
      (fun (n : ℕ) ω ↦ √(breslowInformation (T n ω) (δ n ω) (g n ω) / n)) atTop
      (fun _ ↦ √(v : ℝ)))
    (hinfo_meas : ∀ n : ℕ, AEMeasurable
      (fun ω ↦ √(breslowInformation (T n ω) (δ n ω) (g n ω) / n)) P) :
    Tendsto (fun n : ℕ ↦ P.real {ω | logRankRejects (T n ω) (δ n ω) (g n ω) z}) atTop
      (𝓝 (1 - (gaussianReal 0 1).real (Set.Icc (-z) z))) := by
  have hacc := tendsto_measureReal_abs_le_mul hv z hlim hZ hinfo hinfo_meas
  refine (hacc.const_sub 1).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hmeas : NullMeasurableSet {ω | |observedMinusExpected (T n ω) (δ n ω) (g n ω) / √(n : ℝ)|
      ≤ z * √(breslowInformation (T n ω) (δ n ω) (g n ω) / n)} P :=
    ((hlim.forall_aemeasurable n).prodMk (hinfo_meas n)).nullMeasurable
      (measurableSet_le (by fun_prop) (by fun_prop) :
        MeasurableSet {p : ℝ × ℝ | |p.1| ≤ z * p.2})
  rw [← probReal_compl_eq_one_sub₀ hmeas]
  congr 1
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, logRankRejects]
  rw [Real.sqrt_div' _ (Nat.cast_nonneg n), abs_div, abs_of_pos hsq, mul_div_assoc',
    div_lt_div_iff_of_pos_right hsq]

/-! ### Cox Wald intervals -/

/-- **Pointwise asymptotic coverage of the Cox Wald interval.** For a scalar-covariate Cox
model with true coefficient `β` and estimator `βhat n` (for instance the partial-likelihood
maximizer), take as hypotheses the limit `√n (βhat n - β) ⟶ N(0, v)` with
`v ≠ 0` and consistency of the model-based standard deviation `√(n / I_n(βhat n)) ⟶ √v`,
where `I_n = coxInformation`. Then the Wald interval
`βhat n ± z / √(I_n(βhat n))` covers `β` with probability tending to the standard-normal
mass of `[-z, z]`. -/
theorem tendsto_coverage_cox_waldInterval {T : (n : ℕ) → Ω → Fin n → ℝ}
    {δ : (n : ℕ) → Ω → Fin n → Bool} {x : (n : ℕ) → Ω → Fin n → ℝ} {βhat : ℕ → Ω → ℝ} {β : ℝ}
    {Z : Ω' → ℝ} {v : NNReal} (hv : v ≠ 0) (z : ℝ)
    (hlim : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β)) atTop Z
      (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hinfo : TendstoInMeasure P
      (fun (n : ℕ) ω ↦ √(n / coxInformation (T n ω) (δ n ω) (x n ω) (βhat n ω))) atTop
      (fun _ ↦ √(v : ℝ)))
    (hinfo_meas : ∀ n : ℕ, AEMeasurable
      (fun ω ↦ √(n / coxInformation (T n ω) (δ n ω) (x n ω) (βhat n ω))) P) :
    Tendsto (fun n : ℕ ↦ P.real {ω | β ∈ waldInterval (βhat n ω)
        (1 / √(coxInformation (T n ω) (δ n ω) (x n ω) (βhat n ω))) z}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc (-z) z))) := by
  refine (tendsto_coverage_waldInterval hv z hlim hZ hinfo hinfo_meas).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsq : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [Real.sqrt_div (Nat.cast_nonneg n), div_div, mul_comm, ← div_div, div_self hsq]

/-! ### Simultaneous confidence bands on a finite time grid -/

/-- The simultaneous Wald band on a finite grid `ι` of time points: the functions `f : ι → ℝ`
with `f j ∈ waldInterval (est j) (se j) z` for every grid point `j` at once. -/
def gridBand {ι : Type*} (est se : ι → ℝ) (z : ℝ) : Set (ι → ℝ) :=
  {f | ∀ j, f j ∈ waldInterval (est j) (se j) z}

/-- The closed simultaneous studentized region `{(x, s) | ∀ j, |x j| ≤ z * s j}`. -/
private def bandRegion (ι : Type*) (z : ℝ) : Set ((ι → ℝ) × (ι → ℝ)) :=
  {p | ∀ j, |p.1 j| ≤ z * p.2 j}

private theorem isClosed_bandRegion (ι : Type*) (z : ℝ) : IsClosed (bandRegion ι z) := by
  rw [bandRegion, Set.ofPred_forall]
  exact isClosed_iInter fun j ↦ isClosed_le (by fun_prop) (by fun_prop)

private theorem measurableSet_bandRegion (ι : Type*) [Countable ι] (z : ℝ) :
    MeasurableSet (bandRegion ι z) := by
  rw [bandRegion, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j ↦ measurableSet_le (by fun_prop) (by fun_prop)

private theorem frontier_bandRegion_subset (ι : Type*) [Finite ι] (z : ℝ) :
    frontier (bandRegion ι z) ⊆ ⋃ j, {p : (ι → ℝ) × (ι → ℝ) | |p.1 j| = z * p.2 j} := by
  intro p hp
  have hcl : p ∈ bandRegion ι z := (isClosed_bandRegion ι z).frontier_subset hp
  have hopen : IsOpen {q : (ι → ℝ) × (ι → ℝ) | ∀ j, |q.1 j| < z * q.2 j} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_lt (by fun_prop) (by fun_prop)
  have hnot : ¬ ∀ j, |p.1 j| < z * p.2 j := fun h ↦
    hp.2 (interior_maximal (show {q : (ι → ℝ) × (ι → ℝ) | ∀ j, |q.1 j| < z * q.2 j} ⊆
      bandRegion ι z from fun q hq j ↦ (hq j).le) hopen h)
  simp only [not_forall, not_lt] at hnot
  obtain ⟨j, hj⟩ := hnot
  exact Set.mem_iUnion.2 ⟨j, le_antisymm (hcl j) hj⟩

omit [IsProbabilityMeasure P'] in
/-- A random variable with a nondegenerate centered Gaussian law hits `{|x| = c}` with
probability zero. -/
private theorem hasLaw_abs_eq_null {Y : Ω' → ℝ} {v : NNReal} (hY : HasLaw Y (gaussianReal 0 v) P')
    (hv : v ≠ 0) (c : ℝ) : P' {ω | |Y ω| = c} = 0 := by
  have h := gaussianReal_abs_eq_null hv c
  rw [← hY.map_eq, Measure.map_apply_of_aemeasurable hY.aemeasurable
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))] at h
  exact h

/-- **Simultaneous asymptotic coverage of a grid band.** Take as hypothesis the finite-grid marginal
of the process-level limit, `(√n (est n j - A j))_j ⟶ Z` in distribution, where each coordinate
`Z j` is a nondegenerate centered Gaussian with variance `v j`, together with consistent
coordinatewise standard deviations `se n ⟶ (√(v j))_j` in probability. Then the probability that
the band `gridBand (est n) (se n / √n) z` contains the whole target `A` tends to the joint limit
probability `P' (∀ j, |Z j| ≤ z √(v j))`. No dependence structure of `Z` beyond its marginals is
used; the limit value depends on the joint law of `Z`. -/
theorem tendsto_coverage_gridBand {ι : Type*} [Fintype ι] {est se : ℕ → Ω → ι → ℝ}
    {A : ι → ℝ} {Z : Ω' → ι → ℝ} {v : ι → NNReal} (hv : ∀ j, v j ≠ 0) (z : ℝ)
    (hlim : TendstoInDistribution (fun (n : ℕ) ω j ↦ √(n : ℝ) * (est n ω j - A j)) atTop Z
      (fun _ ↦ P) P')
    (hZ : ∀ j, HasLaw (fun ω ↦ Z ω j) (gaussianReal 0 (v j)) P')
    (hse : TendstoInMeasure P se atTop (fun _ j ↦ √(v j : ℝ)))
    (hse_meas : ∀ n, AEMeasurable (se n) P) :
    Tendsto (fun n : ℕ ↦ P.real {ω | A ∈ gridBand (est n ω) (fun j ↦ se n ω j / √(n : ℝ)) z})
      atTop (𝓝 (P'.real {ω | ∀ j, |Z ω j| ≤ z * √(v j : ℝ)})) := by
  have hpair := hlim.prodMk_of_tendstoInMeasure_const _ se Z hse hse_meas
  have hnull : P'.map (fun ω ↦ (Z ω, fun j ↦ √(v j : ℝ))) (frontier (bandRegion ι z)) = 0 := by
    refine measure_mono_null (frontier_bandRegion_subset ι z) (measure_iUnion_null fun j ↦ ?_)
    rw [Measure.map_apply_of_aemeasurable (hlim.aemeasurable_limit.prodMk aemeasurable_const)
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))]
    exact hasLaw_abs_eq_null (hZ j) (hv j) (z * √(v j : ℝ))
  have hport := tendsto_measureReal_preimage_of_tendstoInDistribution hpair
    (measurableSet_bandRegion ι z) hnull
  refine hport.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  congr 1
  ext ω
  exact forall_congr' fun j ↦ (mem_waldInterval_div_sqrt_iff hn).symm

/-- **Simultaneous coverage is bounded by pointwise coverage.** The simultaneous limit
coverage of the grid band never exceeds the pointwise limit coverage at any grid point, so a
pointwise critical value cannot raise simultaneous coverage above the pointwise level.
Equality is possible (e.g. perfectly correlated coordinates). -/
theorem gridBand_limit_le_pointwise {ι : Type*} {Z : Ω' → ι → ℝ} {v : ι → NNReal}
    (hv : ∀ j, v j ≠ 0) (hZ : ∀ j, HasLaw (fun ω ↦ Z ω j) (gaussianReal 0 (v j)) P')
    (z : ℝ) (j : ι) :
    P'.real {ω | ∀ j, |Z ω j| ≤ z * √(v j : ℝ)} ≤ (gaussianReal 0 1).real (Set.Icc (-z) z) := by
  rw [← gaussianReal_real_abs_le_mul_sqrt (hv j) z,
    ← (hZ j).measureReal_eq (p := fun x ↦ |x| ≤ z * √(v j : ℝ))
      (measurableSet_le (by fun_prop) (by fun_prop))]
  exact measureReal_mono (fun ω hω ↦ hω j) (measure_ne_top _ _)

/-- **Bonferroni lower bound for the simultaneous limit.** On a grid of `card ι` points, the
simultaneous limit coverage is at least `1 - card ι * (1 - (pointwise limit coverage))`. -/
theorem one_sub_card_mul_le_gridBand_limit {ι : Type*} [Fintype ι] {Z : Ω' → ι → ℝ}
    {v : ι → NNReal} (hv : ∀ j, v j ≠ 0)
    (hZ : ∀ j, HasLaw (fun ω ↦ Z ω j) (gaussianReal 0 (v j)) P') (z : ℝ) :
    1 - Fintype.card ι * (1 - (gaussianReal 0 1).real (Set.Icc (-z) z)) ≤
      P'.real {ω | ∀ j, |Z ω j| ≤ z * √(v j : ℝ)} := by
  have hmeas : ∀ j, NullMeasurableSet {ω | |Z ω j| ≤ z * √(v j : ℝ)} P' := fun j ↦
    (hZ j).aemeasurable.nullMeasurable
      (measurableSet_le (by fun_prop) (by fun_prop) : MeasurableSet {x : ℝ | |x| ≤ z * √(v j : ℝ)})
  have hfail : ∀ j, P'.real {ω | |Z ω j| ≤ z * √(v j : ℝ)}ᶜ =
      1 - (gaussianReal 0 1).real (Set.Icc (-z) z) := fun j ↦ by
    rw [probReal_compl_eq_one_sub₀ (hmeas j), ← gaussianReal_real_abs_le_mul_sqrt (hv j) z,
      ← (hZ j).measureReal_eq (p := fun x ↦ |x| ≤ z * √(v j : ℝ))
        (measurableSet_le (by fun_prop) (by fun_prop))]
  have hjoint : {ω | ∀ j, |Z ω j| ≤ z * √(v j : ℝ)} = ⋂ j, {ω | |Z ω j| ≤ z * √(v j : ℝ)} :=
    Set.ofPred_forall _
  have hcompl : {ω | ∀ j, |Z ω j| ≤ z * √(v j : ℝ)}ᶜ =
      ⋃ j ∈ (Finset.univ : Finset ι), {ω | |Z ω j| ≤ z * √(v j : ℝ)}ᶜ := by
    rw [hjoint, Set.compl_iInter]
    simp
  have hub := measureReal_biUnion_finset_le (μ := P') (Finset.univ : Finset ι)
    (fun j ↦ {ω | |Z ω j| ≤ z * √(v j : ℝ)}ᶜ)
  simp only [hfail, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hub
  have hback := probReal_compl_eq_one_sub₀ (μ := P') (s := {ω | ∀ j, |Z ω j| ≤ z * √(v j : ℝ)})
    (by rw [hjoint]; exact NullMeasurableSet.iInter hmeas)
  rw [hcompl] at hback
  linarith

end MathlibExt.Probability.Statistics.ProcessInference

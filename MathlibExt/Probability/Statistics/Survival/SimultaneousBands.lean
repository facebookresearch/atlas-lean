/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import MathlibExt.Probability.Quantile
public import MathlibExt.Probability.Statistics.Slutsky
public import MathlibExt.Probability.Statistics.Survival.AalenJohansenCLT

/-!
# Simultaneous confidence bands on a finite grid

Hall–Wellner-type simultaneous confidence bands for a survival-type curve `θ` (a Kaplan–Meier
survival curve or a Nelson–Aalen cumulative hazard) evaluated on a finite grid `ι`. The band
around an estimate `est` is `est i ± c · w i / √n` at every grid point `i` simultaneously, for a
positive weight function `w` and a critical value `c`. Covering `θ` at every grid point is the
event that the scaled weighted sup statistic `√n · max_i |est i - θ i| / w i` is at most `c`; the
asymptotic coverage follows from a grid limit `√n (est - θ) → Z` by the continuous mapping theorem
for the sup norm, together with Slutsky's theorem for estimated weights and critical values.

## Source receipt

* **Named result:** the Hall–Wellner confidence band for a survival curve from censored data:
  `Ŝ(t) ± c_α n^{-1/2} Ŝ(t) (1 + σ̂²(t))`, with asymptotic simultaneous coverage `1 - α` when
  `c_α` is the upper-`α` point of the limiting weighted sup, which the transformation
  `K = σ² / (1 + σ²)` turns into a Brownian-bridge sup (W. J. Hall and J. A. Wellner,
  *Confidence bands for a survival curve from censored data*, Biometrika 67 (1980), 133–143).
  The analogous Nelson–Aalen band is `Λ̂(t) ± c_α n^{-1/2} (1 + σ̂²(t))`.
* **Textbook form:** J. P. Klein and M. L. Moeschberger, *Survival Analysis: Techniques for
  Censored and Truncated Data*, 2nd ed., Springer (2003), Section 4.4 (confidence bands for the
  survival function: Hall–Wellner and equal-precision bands, and why bands are wider than
  pointwise intervals).
* **Formalized here:** the finite-grid version. The band coverage limit is
  `tendsto_coverage_simultaneousBand`; the exact-level statement with the quantile critical value
  is `tendsto_coverage_simultaneousBand_criticalValue`; the Hall–Wellner transformation to the
  Brownian-bridge covariance is `covariance_div_hallWellner_nelsonAalen` and
  `covariance_div_hallWellner_kaplanMeier`, and to the Brownian-bridge law is
  `map_div_hallWellner_eq_multivariateGaussian`.

## Main definitions

* `weightedSup w v`: the statistic `max_i |v i / w i| = max_i |v i| / |w i|`, the sup norm of
  `v / w` (a zero weight contributes `0`); for positive weights it is `max_i |v i| / w i`.
* `simultaneousBand est w c n`: curves `f` with `|est i - f i| ≤ c · w i / √n` for all `i`.
* `pointwiseInterval est w c n i`: the same condition at the single grid point `i`.
* `criticalValue μ α`: the `(1 - α)`-quantile `cdfQuantile μ (1 - α)` of a real law `μ`.
* `hallWellnerTime σ²`: the Hall–Wellner time `σ² / (1 + σ²) ∈ [0, 1)`.
* `hallWellnerCov σ²`: the Brownian-bridge covariance matrix `K(σ²(min i j)) (1 - K(σ²(max i j)))`.

## Main results

* `mem_simultaneousBand_iff`: coverage of the band is `weightedSup w (√n • (est - θ)) ≤ c`.
* `tendsto_coverage_simultaneousBand`: with grid limit `√n (est n - θ) → Z`, estimated weights
  `ŵ n → w > 0` and estimated critical values `ĉ n → c` in probability, and no atom of
  `max_i |Z i| / w i` at `c`, the simultaneous coverage tends to `P'(max_i |Z i| / w i ≤ c)`.
  `tendsto_coverage_simultaneousBand_const` is the known-weight special case.
* `tendsto_coverage_simultaneousBand_criticalValue`: if the limiting weighted sup has an
  atomless law and `ĉ n` converges to its `criticalValue`, coverage tends to `1 - α`
  (`cdf_criticalValue`, `measure_le_criticalValue`).
* **Simultaneous versus pointwise.** `measure_simultaneous_le_pointwise` (every sample size) and
  `measure_weightedSup_le_le` (in the limit): simultaneous coverage is at most the pointwise
  coverage at any grid point; `tendsto_coverage_pointwiseInterval` gives the pointwise limit.
  Equality cases: `simultaneousBand_eq_of_subsingleton` (one grid point),
  `measure_simultaneous_eq_pointwise_iff` (characterisation), and
  `measure_weightedSup_le_eq_of_proportional` (a perfectly correlated limit `Z = Z₀ • w`).
  `measure_not_simultaneous_le_sum` is the Bonferroni bound in the other direction, and
  `measure_weightedSup_le_le_of_pointwise_level` says a pointwise-calibrated `c` covers at most
  `1 - α` simultaneously.
* `measure_weightedSup_le_ge_of_le`: a critical value for a dominating continuum sup (as in the
  Hall–Wellner tables) is conservative on the grid.
* `covariance_div_hallWellner_nelsonAalen`, `covariance_div_hallWellner_kaplanMeier`: if the grid
  limit has the Gaussian-martingale covariance `Cov(Z i, Z j) = σ²(min i j)`, the Hall–Wellner
  weighted limit has the Brownian-bridge covariance `K i (1 - K j)`, `i ≤ j`, `K = σ²/(1 + σ²)`.
* `map_div_hallWellner_eq_multivariateGaussian`: if moreover the grid limit is a centered
  Gaussian vector, the Hall–Wellner weighted limit has law
  `multivariateGaussian 0 (hallWellnerCov σ2)`, the law of a Brownian bridge at the times `K i`;
  so the limiting weighted sup and its critical value depend only on the times `K i`.
* `tendsto_coverage_kaplanMeierBand_indepCauseLaw`: the band coverage limit for the
  Kaplan–Meier estimator on the grid `{j ≤ m}` under independent censoring, from the merged
  fixed-grid joint CLT `tendstoInDistribution_estimator_indepCauseLaw`, whose centered
  linear-combination laws it keeps for the Kaplan–Meier grid limit.

## Scope

Finite grid only; no convergence in `D[0, τ]`. The Nelson–Aalen grid limit is a hypothesis
(`hZ`), not derived here. The Hall–Wellner law identification
(`map_div_hallWellner_eq_multivariateGaussian`) is stated for the Nelson–Aalen weighting `1 + σ²`
and a centered Gaussian grid limit with the Gaussian-martingale covariance; for the Kaplan–Meier
weighting `S (1 + σ²)` only the covariance identity is stated (the weighted Kaplan–Meier limit is
`-Z / (1 + σ²)`). The closed form of `σ²` for the Kaplan–Meier limit of
`tendsto_coverage_kaplanMeierBand_indepCauseLaw` is not derived. Absence of atoms of the limiting
weighted sup at `c` is a hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.SimultaneousBands

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {ι : Type*}

/-- The **weighted sup statistic** `max_i |v i / w i| = max_i |v i| / |w i|` of a vector `v` on
the finite grid `ι` with weight function `w`: the sup norm of `v / w`. The weight enters through its
absolute value, and a zero weight contributes `0` (Lean's `x / 0 = 0`). For positive weights, as in
the band theorems, this is `max_i |v i| / w i`. -/
noncomputable def weightedSup [Fintype ι] (w v : ι → ℝ) : ℝ :=
  ‖fun i => v i / w i‖

/-- The **simultaneous confidence band** of half-width `c · w i / √n` around the estimate
`est` on the grid `ι`: the set of curves `f` with `|est i - f i| ≤ c · w i / √n` at every grid
point `i` at once. -/
def simultaneousBand (est w : ι → ℝ) (c : ℝ) (n : ℕ) : Set (ι → ℝ) :=
  {f | ∀ i, |est i - f i| ≤ c * w i / √(n : ℝ)}

/-- The **pointwise confidence interval** at the single grid point `i`, with the same half-width
`c · w i / √n` as `simultaneousBand`. -/
def pointwiseInterval (est w : ι → ℝ) (c : ℝ) (n : ℕ) (i : ι) : Set ℝ :=
  {x | |est i - x| ≤ c * w i / √(n : ℝ)}

theorem weightedSup_nonneg [Fintype ι] (w v : ι → ℝ) : 0 ≤ weightedSup w v := norm_nonneg _

theorem abs_div_le_weightedSup [Fintype ι] (w v : ι → ℝ) (i : ι) : |v i / w i| ≤ weightedSup w v :=
  norm_le_pi_norm (fun i => v i / w i) i

/-- For fixed weights, the weighted sup statistic is continuous in the vector. -/
theorem continuous_weightedSup [Fintype ι] (w : ι → ℝ) : Continuous (weightedSup w) :=
  continuous_norm.comp
    (continuous_pi fun i => (continuous_apply (A := fun _ : ι => ℝ) i).div_const (w i))

/-- The weighted sup statistic is the sup norm of `v * w⁻¹`. -/
theorem weightedSup_eq_norm_mul_inv [Fintype ι] (w v : ι → ℝ) : weightedSup w v = ‖v * w⁻¹‖ := by
  simp only [weightedSup, div_eq_mul_inv]
  rfl

/-- Coverage of the simultaneous band is the event that the scaled weighted sup statistic is at
most the critical value. -/
theorem mem_simultaneousBand_iff [Fintype ι] [Nonempty ι] {est w θ : ι → ℝ} (hw : ∀ i, 0 < w i)
    {c : ℝ} {n : ℕ} (hn : 0 < n) :
    θ ∈ simultaneousBand est w c n ↔ weightedSup w (√(n : ℝ) • (est - θ)) ≤ c := by
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  rcases lt_or_ge c 0 with hc | hc
  · obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine iff_of_false (fun h => ?_) (fun h => ?_)
    · have h1 := h i₀
      have h2 : c * w i₀ / √(n : ℝ) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc (hw i₀)) hs
      exact absurd (h1.trans_lt h2) (not_lt.2 (abs_nonneg _))
    · exact absurd ((weightedSup_nonneg _ _).trans h) (not_le.2 hc)
  · unfold weightedSup simultaneousBand
    rw [pi_norm_le_iff_of_nonneg hc]
    refine forall_congr' fun i => ?_
    rw [Real.norm_eq_abs, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_div, abs_mul,
      abs_of_pos hs, abs_of_pos (hw i), div_le_iff₀ (hw i), le_div_iff₀ hs]
    constructor <;> intro h <;> linarith

/-! ### Simultaneous versus pointwise coverage at a fixed sample size -/

/-- The simultaneous band is the intersection over the grid of the pointwise intervals. -/
theorem simultaneousBand_eq_iInter (est w : ι → ℝ) (c : ℝ) (n : ℕ) :
    simultaneousBand est w c n = ⋂ i, (fun f : ι → ℝ => f i) ⁻¹' pointwiseInterval est w c n i := by
  ext f
  simp [simultaneousBand, pointwiseInterval]

/-- **Equality case on a one-point grid.** If the grid has a single point, the simultaneous band
is the pointwise interval. -/
theorem simultaneousBand_eq_of_subsingleton [Subsingleton ι] (est w : ι → ℝ) (c : ℝ) (n : ℕ)
    (i : ι) :
    simultaneousBand est w c n = (fun f : ι → ℝ => f i) ⁻¹' pointwiseInterval est w c n i := by
  ext f
  refine ⟨fun h => h i, fun h j => ?_⟩
  rw [Subsingleton.elim j i]
  exact h

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Simultaneous coverage is at most pointwise coverage.** For a random estimate `est` and
random weights `w` (any sample size `n`, any critical value `c`), the probability that the band
covers the whole curve `θ` is at most the probability that the interval at any single grid point
`i` covers `θ i`. -/
theorem measure_simultaneous_le_pointwise (P : Measure Ω) (est w : Ω → ι → ℝ) (θ : ι → ℝ)
    (c : ℝ) (n : ℕ) (i : ι) :
    P {ω | θ ∈ simultaneousBand (est ω) (w ω) c n} ≤
      P {ω | θ i ∈ pointwiseInterval (est ω) (w ω) c n i} :=
  measure_mono fun _ h => h i

/-- **Bonferroni lower bound.** The simultaneous non-coverage probability is at most the sum
of the pointwise non-coverage probabilities. -/
theorem measure_not_simultaneous_le_sum [Fintype ι] (P : Measure Ω) (est w : Ω → ι → ℝ) (θ : ι → ℝ)
    (c : ℝ) (n : ℕ) :
    P {ω | θ ∉ simultaneousBand (est ω) (w ω) c n} ≤
      ∑ i, P {ω | θ i ∉ pointwiseInterval (est ω) (w ω) c n i} := by
  have h : {ω | θ ∉ simultaneousBand (est ω) (w ω) c n} =
      ⋃ i, {ω | θ i ∉ pointwiseInterval (est ω) (w ω) c n i} := by
    ext ω
    simp [simultaneousBand, pointwiseInterval]
  rw [h]
  exact measure_iUnion_fintype_le P _

/-- **Equality characterisation.** For a finite measure, simultaneous coverage equals the
pointwise coverage at `i` exactly when, almost surely, covering `θ i` forces covering the whole
curve. -/
theorem measure_simultaneous_eq_pointwise_iff (P : Measure Ω) [IsFiniteMeasure P]
    (est w : Ω → ι → ℝ) (θ : ι → ℝ) (c : ℝ) (n : ℕ) (i : ι)
    (hm : NullMeasurableSet {ω | θ ∈ simultaneousBand (est ω) (w ω) c n} P) :
    P {ω | θ ∈ simultaneousBand (est ω) (w ω) c n} =
        P {ω | θ i ∈ pointwiseInterval (est ω) (w ω) c n i} ↔
      P ({ω | θ i ∈ pointwiseInterval (est ω) (w ω) c n i} \
        {ω | θ ∈ simultaneousBand (est ω) (w ω) c n}) = 0 := by
  have hsub : {ω | θ ∈ simultaneousBand (est ω) (w ω) c n} ⊆
      {ω | θ i ∈ pointwiseInterval (est ω) (w ω) c n i} := fun _ h => h i
  rw [measure_sdiff hsub hm (measure_ne_top _ _), tsub_eq_zero_iff_le]
  exact ⟨fun h => h.ge, fun h => le_antisymm (measure_simultaneous_le_pointwise P est w θ c n i) h⟩

/-! ### Asymptotic coverage -/

section Asymptotic

variable {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- Portmanteau at a continuity point: if `T n → T'` in distribution and `T'` has no atom at
`c`, then `P(T n ≤ c) → P'(T' ≤ c)`. -/
private theorem tendsto_measure_le_of_tendstoInDistribution {T : ℕ → Ω → ℝ} {T' : Ω' → ℝ}
    (h : TendstoInDistribution T atTop T' (fun _ => P) P') {c : ℝ}
    (hc : P' {ω | T' ω = c} = 0) :
    Tendsto (fun n => P {ω | T n ω ≤ c}) atTop (𝓝 (P' {ω | T' ω ≤ c})) := by
  have hfront : ((⟨P'.map T', inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ)
      (frontier (Iic c)) = 0 := by
    rw [frontier_Iic]
    change P'.map T' {c} = 0
    rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit (measurableSet_singleton c)]
    exact hc
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto hfront
  simp only [ProbabilityMeasure.coe_mk] at key
  rw [Measure.map_apply_of_aemeasurable h.aemeasurable_limit measurableSet_Iic] at key
  refine key.congr fun n => ?_
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) measurableSet_Iic]
  rfl

omit [IsProbabilityMeasure P] in
/-- If the events `A n` and `B n` agree off exceptional events `bad n` of vanishing probability,
then `P (A n)` and `P (B n)` have the same limit. -/
private theorem tendsto_measure_of_agree_off {A B bad : ℕ → Set Ω} {L : ENNReal}
    (hB : Tendsto (fun n => P (B n)) atTop (𝓝 L))
    (hbad : Tendsto (fun n => P (bad n)) atTop (𝓝 0))
    (hAB : ∀ᶠ n in atTop, A n \ bad n ⊆ B n) (hBA : ∀ᶠ n in atTop, B n \ bad n ⊆ A n) :
    Tendsto (fun n => P (A n)) atTop (𝓝 L) := by
  have hup : Tendsto (fun n => P (B n) + P (bad n)) atTop (𝓝 (L + 0)) :=
    hB.add hbad
  have hlo : Tendsto (fun n => P (B n) - P (bad n)) atTop (𝓝 (L - 0)) :=
    ENNReal.Tendsto.sub hB hbad (Or.inr ENNReal.zero_ne_top)
  rw [add_zero] at hup
  rw [tsub_zero] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [hBA] with n hn
    rw [tsub_le_iff_right]
    calc P (B n) ≤ P (B n \ bad n) + P (bad n) :=
          (measure_mono (subset_sdiff_union _ _)).trans (measure_union_le _ _)
      _ ≤ P (A n) + P (bad n) := by gcongr
  · filter_upwards [hAB] with n hn
    calc P (A n) ≤ P (A n \ bad n) + P (bad n) :=
          (measure_mono (subset_sdiff_union _ _)).trans (measure_union_le _ _)
      _ ≤ P (B n) + P (bad n) := by gcongr

omit [IsProbabilityMeasure P] in
/-- If random weights converge in probability to a strictly positive weight function, the
probability that some estimated weight is nonpositive tends to zero. -/
private theorem tendsto_measure_exists_nonpos [Fintype ι] {ŵ : ℕ → Ω → ι → ℝ} {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hŵ : TendstoInMeasure P ŵ atTop (fun _ => w)) :
    Tendsto (fun n => P {ω | ∃ i, ŵ n ω i ≤ 0}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist] at hŵ
  have hsum : Tendsto (fun n => ∑ i, P {ω | w i ≤ dist (ŵ n ω) w}) atTop (𝓝 (∑ _i : ι, 0)) :=
    tendsto_finsetSum _ fun i _ => hŵ (w i) (hw i)
  rw [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
    fun n => ?_
  have hsub : {ω | ∃ i, ŵ n ω i ≤ 0} ⊆ ⋃ i, {ω | w i ≤ dist (ŵ n ω) w} := by
    rintro ω ⟨i, hi⟩
    refine mem_iUnion.2 ⟨i, ?_⟩
    have h1 : dist (ŵ n ω i) (w i) ≤ dist (ŵ n ω) w := dist_le_pi_dist _ _ i
    rw [Real.dist_eq] at h1
    change w i ≤ dist (ŵ n ω) w
    have h2 : w i - ŵ n ω i ≤ |ŵ n ω i - w i| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  exact (measure_mono hsub).trans (measure_iUnion_fintype_le P _)

/-- **Asymptotic coverage of the simultaneous band with estimated weights and an estimated
critical value.** Suppose that on the finite grid `ι` the scaled estimation error
`√n (est n - θ)` converges in distribution to `Z` (the grid limit), the estimated weights
`ŵ n` converge in probability to a strictly positive weight function `w`, and the estimated
critical values `ĉ n` converge in probability to `c`. If the limiting weighted sup statistic
`max_i |Z i| / w i` has no atom at `c`, the probability that the band
`est n ± ĉ n · ŵ n / √n` covers `θ` at every grid point tends to `P'(max_i |Z i| / w i ≤ c)`.
The proof is the sup-norm continuous mapping theorem combined with Slutsky's theorem. -/
theorem tendsto_coverage_simultaneousBand [Fintype ι] [Nonempty ι] {est : ℕ → Ω → ι → ℝ}
    {θ : ι → ℝ} {Z : Ω' → ι → ℝ}
    (hZ : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (est n ω - θ)) atTop Z
      (fun _ => P) P')
    {ŵ : ℕ → Ω → ι → ℝ} {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hŵ : TendstoInMeasure P ŵ atTop (fun _ => w)) (hŵm : ∀ n, AEMeasurable (ŵ n) P)
    {ĉ : ℕ → Ω → ℝ} {c : ℝ} (hĉ : TendstoInMeasure P ĉ atTop (fun _ => c))
    (hĉm : ∀ n, AEMeasurable (ĉ n) P) (hatom : P' {ω | weightedSup w (Z ω) = c} = 0) :
    Tendsto (fun n => P {ω | θ ∈ simultaneousBand (est n ω) (ŵ n ω) (ĉ n ω) n}) atTop
      (𝓝 (P' {ω | weightedSup w (Z ω) ≤ c})) := by
  -- inverse weights converge in probability
  have hcont : ContinuousAt (fun u : ι → ℝ => u⁻¹) w :=
    tendsto_pi_nhds.2 fun i => ((continuous_apply i).tendsto w).inv₀ (hw i).ne'
  have hinv := TendstoInMeasure.comp_const_of_continuousAt hcont hŵ
  have hinvm : ∀ n, AEMeasurable (fun ω => (ŵ n ω)⁻¹) P := fun n =>
    (hŵm n).inv
  -- sup-norm continuous mapping + Slutsky for the weights
  have hT := hZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (ι → ℝ) × (ι → ℝ) => ‖p.1 * p.2‖) (by fun_prop) hinv hinvm
  -- Slutsky for the critical value
  have hneg := TendstoInMeasure.comp_const_of_continuousAt (f := fun x : ℝ => -x)
    continuous_neg.continuousAt hĉ
  have hT2 := hT.add_of_tendstoInMeasure_const hneg fun n => (hĉm n).neg
  have hlimit : ∀ ω, ‖Z ω * w⁻¹‖ = weightedSup w (Z ω) := fun ω =>
    (weightedSup_eq_norm_mul_inv w (Z ω)).symm
  have hatom' : P' {ω | ‖Z ω * w⁻¹‖ + -c = 0} = 0 := by
    simpa only [hlimit, add_neg_eq_zero] using hatom
  have hB := tendsto_measure_le_of_tendstoInDistribution hT2 hatom'
  simp only [hlimit, Pi.add_apply, add_neg_le_iff_le_add, zero_add] at hB
  refine tendsto_measure_of_agree_off hB (tendsto_measure_exists_nonpos hw hŵ) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rintro ω ⟨hA, hbad⟩
    have hpos : ∀ i, 0 < ŵ n ω i := fun i => not_le.1 fun h => hbad ⟨i, h⟩
    have := (mem_simultaneousBand_iff hpos hn).1 hA
    rw [weightedSup_eq_norm_mul_inv] at this
    exact this
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rintro ω ⟨hB, hbad⟩
    have hpos : ∀ i, 0 < ŵ n ω i := fun i => not_le.1 fun h => hbad ⟨i, h⟩
    refine (mem_simultaneousBand_iff hpos hn).2 ?_
    rw [weightedSup_eq_norm_mul_inv]
    exact hB

omit [IsProbabilityMeasure P] in
/-- A constant sequence converges in probability to its value. -/
theorem tendstoInMeasure_const_self {E : Type*} [PseudoMetricSpace E] (a : E) :
    TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => a) atTop (fun _ => a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have h : {ω : Ω | ε ≤ dist a a} = ∅ := by
    ext ω
    simp only [dist_self, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact hε
  simp only [h, measure_empty, tendsto_const_nhds]

/-- **Asymptotic coverage with known weights and a fixed critical value** (the oracle band
`est n ± c · w / √n`), from `tendsto_coverage_simultaneousBand`. -/
theorem tendsto_coverage_simultaneousBand_const [Fintype ι] [Nonempty ι]
    {est : ℕ → Ω → ι → ℝ} {θ : ι → ℝ} {Z : Ω' → ι → ℝ}
    (hZ : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (est n ω - θ)) atTop Z
      (fun _ => P) P')
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) {c : ℝ} (hatom : P' {ω | weightedSup w (Z ω) = c} = 0) :
    Tendsto (fun n => P {ω | θ ∈ simultaneousBand (est n ω) w c n}) atTop
      (𝓝 (P' {ω | weightedSup w (Z ω) ≤ c})) :=
  tendsto_coverage_simultaneousBand (ŵ := fun _ _ => w) (ĉ := fun _ _ => c) hZ hw
    (tendstoInMeasure_const_self w) (fun _ => aemeasurable_const)
    (tendstoInMeasure_const_self c) (fun _ => aemeasurable_const) hatom

/-- **Asymptotic pointwise coverage.** Under the hypotheses of
`tendsto_coverage_simultaneousBand`, the interval at the single grid point `i` covers `θ i`
with probability tending to `P'(|Z i| / w i ≤ c)`, provided `|Z i| / w i` has no atom at `c`.
Derived from the simultaneous theorem on the one-point grid. -/
theorem tendsto_coverage_pointwiseInterval [Fintype ι] {est : ℕ → Ω → ι → ℝ} {θ : ι → ℝ}
    {Z : Ω' → ι → ℝ}
    (hZ : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (est n ω - θ)) atTop Z
      (fun _ => P) P')
    {ŵ : ℕ → Ω → ι → ℝ} {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hŵ : TendstoInMeasure P ŵ atTop (fun _ => w)) (hŵm : ∀ n, AEMeasurable (ŵ n) P)
    {ĉ : ℕ → Ω → ℝ} {c : ℝ} (hĉ : TendstoInMeasure P ĉ atTop (fun _ => c))
    (hĉm : ∀ n, AEMeasurable (ĉ n) P) (i : ι) (hatom : P' {ω | |Z ω i / w i| = c} = 0) :
    Tendsto (fun n => P {ω | θ i ∈ pointwiseInterval (est n ω) (ŵ n ω) (ĉ n ω) n i}) atTop
      (𝓝 (P' {ω | |Z ω i / w i| ≤ c})) := by
  have hcoord : Continuous fun v : ι → ℝ => fun _ : Unit => v i := by fun_prop
  have hZ' : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • ((fun _ : Unit => est n ω i) - fun _ => θ i)) atTop
      (fun ω _ => Z ω i) (fun _ => P) P' := hZ.continuous_comp hcoord
  have hŵ' := TendstoInMeasure.comp_const_of_continuousAt hcoord.continuousAt hŵ
  have h := tendsto_coverage_simultaneousBand hZ' (fun _ => hw i) hŵ'
    (fun n => hcoord.measurable.comp_aemeasurable (hŵm n)) hĉ hĉm
    (by simpa only [weightedSup, pi_norm_const, Real.norm_eq_abs] using hatom)
  simpa only [weightedSup, pi_norm_const, Real.norm_eq_abs, simultaneousBand, pointwiseInterval,
    forall_const, mem_ofPred_eq] using h

omit [IsProbabilityMeasure P'] in
/-- **Simultaneous limit coverage is at most pointwise limit coverage**: for every grid point
`i`, `P'(max_j |Z j / w j| ≤ c) ≤ P'(|Z i / w i| ≤ c)`. -/
theorem measure_weightedSup_le_le [Fintype ι] (Z : Ω' → ι → ℝ) (w : ι → ℝ) (c : ℝ) (i : ι) :
    P' {ω | weightedSup w (Z ω) ≤ c} ≤ P' {ω | |Z ω i / w i| ≤ c} :=
  measure_mono fun _ h => (abs_div_le_weightedSup _ _ i).trans h

omit [IsProbabilityMeasure P'] in
/-- **Equality case: a perfectly correlated grid limit.** If the grid limit is proportional to the
weight function, `Z = Z₀ • w`, then simultaneous and pointwise limit coverage coincide at every
grid point. -/
theorem measure_weightedSup_le_eq_of_proportional [Fintype ι] [Nonempty ι] {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) {Z : Ω' → ι → ℝ} {Z₀ : Ω' → ℝ} (hZ : ∀ ω, Z ω = Z₀ ω • w) (c : ℝ)
    (i : ι) :
    P' {ω | weightedSup w (Z ω) ≤ c} = P' {ω | |Z ω i / w i| ≤ c} := by
  have h1 : ∀ ω, weightedSup w (Z ω) = |Z₀ ω| := fun ω => by
    have : (fun j => Z ω j / w j) = fun _ => Z₀ ω := funext fun j => by
      rw [hZ ω, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self (hw j).ne', mul_one]
    rw [weightedSup, this, pi_norm_const, Real.norm_eq_abs]
  have h2 : ∀ ω, |Z ω i / w i| = |Z₀ ω| := fun ω => by
    rw [hZ ω, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self (hw i).ne', mul_one]
  simp only [h1, h2]

end Asymptotic

/-! ### Critical values -/

/-- The **level-`(1 - α)` critical value** of a real law `μ`, meant as the law of the limiting
weighted sup statistic: the `(1 - α)`-quantile `cdfQuantile μ (1 - α)`. -/
noncomputable def criticalValue (μ : Measure ℝ) (α : ℝ) : ℝ :=
  cdfQuantile μ (1 - α)

/-- For an atomless law, the cdf at the critical value is exactly `1 - α`. -/
theorem cdf_criticalValue (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hatom : ∀ x, μ {x} = 0) :
    cdf μ (criticalValue μ α) = 1 - α := by
  have hu : 1 - α ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  set q := criticalValue μ α
  refine le_antisymm ?_ (cdfQuantile_mem μ hu)
  have hlt : ∀ x < q, cdf μ x < 1 - α := fun x hx =>
    not_le.1 fun h => (not_le.2 hx) ((cdfQuantile_le_iff μ hu).2 h)
  have hleft : Function.leftLim (cdf μ) q ≤ 1 - α :=
    le_of_tendsto ((monotone_cdf μ).tendsto_leftLim q)
      (eventually_nhdsWithin_of_forall fun x hx => (hlt x hx).le)
  have hsing : ENNReal.ofReal (cdf μ q - Function.leftLim (cdf μ) q) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf]
    exact hatom q
  rw [ENNReal.ofReal_eq_zero] at hsing
  linarith

section CriticalValue

variable {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- If the statistic `M` has an atomless law, `M` is at most its level-`(1 - α)` critical value
with probability exactly `1 - α`. -/
theorem measure_le_criticalValue {M : Ω' → ℝ} (hM : AEMeasurable M P') {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hatom : ∀ x, P' {ω | M ω = x} = 0) :
    P' {ω | M ω ≤ criticalValue (P'.map M) α} = ENNReal.ofReal (1 - α) := by
  have hatom' : ∀ x, P'.map M {x} = 0 := fun x => by
    rw [Measure.map_apply_of_aemeasurable hM (measurableSet_singleton x)]
    exact hatom x
  rw [← cdf_criticalValue (P'.map M) hα hatom', ofReal_cdf,
    Measure.map_apply_of_aemeasurable hM measurableSet_Iic]
  rfl

/-- **Asymptotically exact simultaneous coverage.** Under the hypotheses of
`tendsto_coverage_simultaneousBand`, if the limiting weighted sup statistic has an atomless law
and the estimated critical values converge in probability to its level-`(1 - α)` critical value,
the simultaneous coverage probability tends to `1 - α`. -/
theorem tendsto_coverage_simultaneousBand_criticalValue [Fintype ι] [Nonempty ι]
    {est : ℕ → Ω → ι → ℝ} {θ : ι → ℝ} {Z : Ω' → ι → ℝ}
    (hZ : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (est n ω - θ)) atTop Z
      (fun _ => P) P')
    {ŵ : ℕ → Ω → ι → ℝ} {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hŵ : TendstoInMeasure P ŵ atTop (fun _ => w)) (hŵm : ∀ n, AEMeasurable (ŵ n) P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hatom : ∀ x, P' {ω | weightedSup w (Z ω) = x} = 0)
    {ĉ : ℕ → Ω → ℝ}
    (hĉ : TendstoInMeasure P ĉ atTop
      (fun _ => criticalValue (P'.map fun ω => weightedSup w (Z ω)) α))
    (hĉm : ∀ n, AEMeasurable (ĉ n) P) :
    Tendsto (fun n => P {ω | θ ∈ simultaneousBand (est n ω) (ŵ n ω) (ĉ n ω) n}) atTop
      (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hM : AEMeasurable (fun ω => weightedSup w (Z ω)) P' :=
    (continuous_weightedSup w).measurable.comp_aemeasurable hZ.aemeasurable_limit
  rw [← measure_le_criticalValue hM hα hatom]
  exact tendsto_coverage_simultaneousBand hZ hw hŵ hŵm hĉ hĉm (hatom _)

omit [IsProbabilityMeasure P'] in
/-- **Pointwise calibration covers at most `1 - α` simultaneously.** If `c` gives limiting pointwise
coverage `1 - α` at some grid point `i`, the limiting simultaneous coverage of the band with the
same `c` is at most `1 - α`. -/
theorem measure_weightedSup_le_le_of_pointwise_level [Fintype ι] (Z : Ω' → ι → ℝ)
    (w : ι → ℝ) {c α : ℝ} (i : ι) (hpt : P' {ω | |Z ω i / w i| ≤ c} = ENNReal.ofReal (1 - α)) :
    P' {ω | weightedSup w (Z ω) ≤ c} ≤ ENNReal.ofReal (1 - α) :=
  hpt ▸ measure_weightedSup_le_le Z w c i

omit [IsProbabilityMeasure P'] in
/-- **Grid bands with a continuum critical value are conservative.** If the grid statistic is
dominated by a continuum statistic `Mcont` (e.g. the sup of the limit process over a whole
interval, as in the Hall–Wellner tables), any `c` with `P'(Mcont ≤ c) ≥ 1 - α` gives limiting
grid coverage at least `1 - α`. -/
theorem measure_weightedSup_le_ge_of_le [Fintype ι] {Z : Ω' → ι → ℝ} {w : ι → ℝ}
    {Mcont : Ω' → ℝ} (hle : ∀ ω, weightedSup w (Z ω) ≤ Mcont ω) {c α : ℝ}
    (hcont : ENNReal.ofReal (1 - α) ≤ P' {ω | Mcont ω ≤ c}) :
    ENNReal.ofReal (1 - α) ≤ P' {ω | weightedSup w (Z ω) ≤ c} :=
  hcont.trans (measure_mono fun ω h => (hle ω).trans h)

end CriticalValue

/-! ### The Hall–Wellner transformation -/

/-- The **Hall–Wellner time transformation** `K = σ² / (1 + σ²)` of a variance value `σ²`. -/
noncomputable def hallWellnerTime (σ2 : ℝ) : ℝ :=
  σ2 / (1 + σ2)

theorem hallWellnerTime_nonneg {σ2 : ℝ} (h : 0 ≤ σ2) : 0 ≤ hallWellnerTime σ2 :=
  div_nonneg h (by linarith)

theorem hallWellnerTime_lt_one {σ2 : ℝ} (h : 0 ≤ σ2) : hallWellnerTime σ2 < 1 := by
  rw [hallWellnerTime, div_lt_one (by linarith)]
  linarith

section HallWellner

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {ι : Type*} [LinearOrder ι]

/-- **Hall–Wellner transformation, Nelson–Aalen form.** Let the grid limit `Z` of the
Nelson–Aalen estimator have the covariance of a Gaussian martingale with variance function
`σ²`, i.e. `Cov(Z i, Z j) = σ²(min i j)`. With the Hall–Wellner weight `1 + σ²`, the weighted
limit `Z i / (1 + σ² i)` has the Brownian-bridge covariance `K i · (1 - K j)` for `i ≤ j`, where
`K = σ² / (1 + σ²)` (`hallWellnerTime`). -/
theorem covariance_div_hallWellner_nelsonAalen {Z : Ω' → ι → ℝ} {σ2 : ι → ℝ}
    (hσ : ∀ i, 0 ≤ σ2 i)
    (hcov : ∀ i j, cov[fun ω => Z ω i, fun ω => Z ω j; P'] = σ2 (min i j)) {i j : ι}
    (hij : i ≤ j) :
    cov[fun ω => Z ω i / (1 + σ2 i), fun ω => Z ω j / (1 + σ2 j); P'] =
      hallWellnerTime (σ2 i) * (1 - hallWellnerTime (σ2 j)) := by
  have hi : 1 + σ2 i ≠ 0 := by linarith [hσ i]
  have hj : 1 + σ2 j ≠ 0 := by linarith [hσ j]
  simp only [div_eq_mul_inv]
  rw [covariance_mul_const_left, covariance_mul_const_right, hcov, min_eq_left hij,
    hallWellnerTime, hallWellnerTime]
  field_simp
  ring

/-- **Hall–Wellner transformation, Kaplan–Meier form.** Under the hypotheses of
`covariance_div_hallWellner_nelsonAalen`, the Kaplan–Meier grid limit `-S · Z` (delta method),
weighted by the Hall–Wellner weight `S (1 + σ²)` with `S ≠ 0`, has the same Brownian-bridge
covariance `K i · (1 - K j)` for `i ≤ j`. -/
theorem covariance_div_hallWellner_kaplanMeier {Z : Ω' → ι → ℝ} {σ2 S : ι → ℝ}
    (hσ : ∀ i, 0 ≤ σ2 i) (hS : ∀ i, S i ≠ 0)
    (hcov : ∀ i j, cov[fun ω => Z ω i, fun ω => Z ω j; P'] = σ2 (min i j)) {i j : ι}
    (hij : i ≤ j) :
    cov[fun ω => -(S i * Z ω i) / (S i * (1 + σ2 i)),
        fun ω => -(S j * Z ω j) / (S j * (1 + σ2 j)); P'] =
      hallWellnerTime (σ2 i) * (1 - hallWellnerTime (σ2 j)) := by
  have hi : 1 + σ2 i ≠ 0 := by linarith [hσ i]
  have hj : 1 + σ2 j ≠ 0 := by linarith [hσ j]
  have h : ∀ l, 1 + σ2 l ≠ 0 → (fun ω => -(S l * Z ω l) / (S l * (1 + σ2 l))) =
      fun ω => Z ω l / (1 + σ2 l) * (-1) := fun l hl => funext fun ω => by
    field_simp [hS l]
  rw [h i hi, h j hj, covariance_mul_const_left, covariance_mul_const_right,
    covariance_div_hallWellner_nelsonAalen hσ hcov hij]
  ring

/-- The **Brownian-bridge covariance matrix** at the Hall–Wellner times: entry `(i, j)` is
`K(σ²(min i j)) · (1 - K(σ²(max i j)))` with `K = hallWellnerTime`. For nondecreasing `σ²` this
is `min(K i, K j) · (1 - max(K i, K j))`, the covariance of a Brownian bridge at the times
`K i`. -/
noncomputable def hallWellnerCov (σ2 : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => hallWellnerTime (σ2 (min i j)) * (1 - hallWellnerTime (σ2 (max i j)))

/-- The covariance identity of `covariance_div_hallWellner_nelsonAalen` for all pairs of grid
points, in matrix form. -/
theorem covariance_div_hallWellner_eq_hallWellnerCov {Z : Ω' → ι → ℝ} {σ2 : ι → ℝ}
    (hσ : ∀ i, 0 ≤ σ2 i)
    (hcov : ∀ i j, cov[fun ω => Z ω i, fun ω => Z ω j; P'] = σ2 (min i j)) (i j : ι) :
    cov[fun ω => Z ω i / (1 + σ2 i), fun ω => Z ω j / (1 + σ2 j); P'] = hallWellnerCov σ2 i j := by
  rcases le_total i j with h | h
  · rw [covariance_div_hallWellner_nelsonAalen hσ hcov h]
    simp [hallWellnerCov, min_eq_left h, max_eq_right h]
  · rw [covariance_comm, covariance_div_hallWellner_nelsonAalen hσ hcov h]
    simp [hallWellnerCov, min_eq_right h, max_eq_left h]

/-- **Hall–Wellner transformation, law level.** Let the grid limit `Z` of the Nelson–Aalen
estimator be a centered Gaussian vector with the Gaussian-martingale covariance
`Cov(Z i, Z j) = σ²(min i j)`. Then the Hall–Wellner weighted limit `(Z i / (1 + σ² i))_i` has
law `multivariateGaussian 0 (hallWellnerCov σ2)`: the law of a Brownian bridge at the times
`K i = σ² i / (1 + σ² i)`. Hence the limiting weighted sup, and so the critical value, depends only
on the times `K i`. -/
theorem map_div_hallWellner_eq_multivariateGaussian [Fintype ι] [DecidableEq ι]
    {Z : Ω' → ι → ℝ} {σ2 : ι → ℝ} (hσ : ∀ i, 0 ≤ σ2 i) (hZ : HasGaussianLaw Z P')
    (hmean : ∀ i, P'[fun ω => Z ω i] = 0)
    (hcov : ∀ i j, cov[fun ω => Z ω i, fun ω => Z ω j; P'] = σ2 (min i j)) :
    P'.map (fun ω => WithLp.toLp 2 (fun i => Z ω i / (1 + σ2 i))) =
      multivariateGaussian 0 (hallWellnerCov σ2) := by
  have : IsProbabilityMeasure P' := hZ.isProbabilityMeasure
  let L : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i => (1 + σ2 i)⁻¹ • ContinuousLinearMap.proj i
  have hY : HasGaussianLaw (fun ω i => Z ω i / (1 + σ2 i)) P' := by
    have h := hZ.map_fun L
    convert h using 2 with ω
    ext i
    simp [L, div_eq_inv_mul]
  have hYv := hY.toLp_pi 2
  have : IsGaussian (P'.map fun ω => WithLp.toLp 2 (fun i => Z ω i / (1 + σ2 i))) :=
    hYv.isGaussian_map
  have hmem : ∀ i, MemLp (fun ω => Z ω i / (1 + σ2 i)) 2 P' := fun i => (hY.eval i).memLp_two
  have hcovY := covariance_div_hallWellner_eq_hallWellnerCov hσ hcov
  have hbilin : ∀ x y : EuclideanSpace ℝ ι,
      covarianceBilin (P'.map fun ω => WithLp.toLp 2 (fun i => Z ω i / (1 + σ2 i))) x y =
        dotProduct x.ofLp ((hallWellnerCov σ2).mulVec y.ofLp) := fun x y => by
    rw [covarianceBilin_apply_pi hmem]
    simp only [hcovY, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hpsd : (hallWellnerCov σ2).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext i j
      simp [Matrix.conjTranspose_apply, hallWellnerCov, min_comm, max_comm]
    · have h0 := (isPosSemidef_covarianceBilin
        (μ := P'.map fun ω => WithLp.toLp 2 (fun i => Z ω i / (1 + σ2 i)))).nonneg
        (WithLp.toLp 2 x)
      simp only [ContinuousLinearMap.toBilinForm_apply, hbilin] at h0
      simpa using h0
  refine IsGaussian.ext ?_ ?_
  · rw [integral_id_multivariateGaussian']
    set μY := P'.map fun ω => WithLp.toLp 2 (fun i => Z ω i / (1 + σ2 i))
    have hint : Integrable id μY := IsGaussian.integrable_id
    ext i
    have h1 := (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).integral_comp_comm hint
    have h2 : (∫ x, id x ∂μY).ofLp i = ∫ x, x.ofLp i ∂μY := by
      simpa using h1.symm
    rw [h2, integral_map hYv.aemeasurable (by fun_prop)]
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, hmean i, zero_mul]
    rfl
  · ext x y
    rw [hbilin, covarianceBilin_multivariateGaussian hpsd]

end HallWellner

/-! ### Kaplan–Meier bands from the fixed-grid joint CLT -/

section KaplanMeier

open MathlibExt.Probability.Statistics.AalenJohansenCLT
open MathlibExt.Probability.Statistics.Censoring MathlibExt.Probability.Statistics.CompetingRisks
open MathlibExt.Probability.Statistics.SurvivalConsistency

variable {k r : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℕ → Ω → (Fin k × Fin r) × Fin k}

/-- **Simultaneous Kaplan–Meier bands on the grid `{j ≤ m}` under independent censoring.**
For i.i.d. subjects with law `indepCauseLaw pTJ pC` and `P(min T C ≥ m) ≠ 0`, there is a centered
Gaussian grid limit `Y` (the Kaplan–Meier block of the joint limit of
`tendstoInDistribution_estimator_indepCauseLaw`): every linear combination `∑_j s j · Y j` has law
`N(0, Var(∑_j s j · ψ j))`, where `ψ j` is the Kaplan–Meier coordinate `(none, j)` of the
influence vector of one subject. Moreover, for all estimated weights
`ŵ n → w > 0` and estimated critical values `ĉ n → c` in probability with
`P(max_j |Y j| / w j = c) = 0`, the band `Ŝ(j) ± ĉ n · ŵ n j / √n`, `j ≤ m`, covers the survival
curve `P(T > j)` at all grid points with probability tending to `P(max_j |Y j| / w j ≤ c)`. -/
theorem tendsto_coverage_kaplanMeierBand_indepCauseLaw (pTJ : PMF (Fin k × Fin r))
    (pC : PMF (Fin k)) (hind : iIndepFun W P)
    (hlaw : ∀ i, HasLaw (W i) (indepCauseLaw pTJ pC) P) (m : Fin k)
    (hm : causeAtRiskMass (indepCauseLaw pTJ pC) m ≠ 0) :
    ∃ Y : EuclideanSpace ℝ (Cell k r) → {j : Fin k // j ≤ m} → ℝ,
      HasGaussianLaw Y (stdGaussian (EuclideanSpace ℝ (Cell k r))) ∧
      (∀ s : {j : Fin k // j ≤ m} → ℝ, HasLaw (fun z => ∑ j, s j * Y z j)
        (gaussianReal 0 (Var[fun ω => ∑ j, s j *
          influence (indepCauseLaw pTJ pC) m (W 0 ω) (none, j); P]).toNNReal)
        (stdGaussian (EuclideanSpace ℝ (Cell k r)))) ∧
      ∀ {ŵ : ℕ → Ω → {j : Fin k // j ≤ m} → ℝ} {w : {j : Fin k // j ≤ m} → ℝ}
        {ĉ : ℕ → Ω → ℝ} {c : ℝ}, (∀ j, 0 < w j) → TendstoInMeasure P ŵ atTop (fun _ => w) →
        (∀ n, AEMeasurable (ŵ n) P) → TendstoInMeasure P ĉ atTop (fun _ => c) →
        (∀ n, AEMeasurable (ĉ n) P) →
        stdGaussian (EuclideanSpace ℝ (Cell k r)) {z | weightedSup w (Y z) = c} = 0 →
        Tendsto (fun n => P {ω | (fun j => target pTJ m (none, j)) ∈
            simultaneousBand (fun j => estimator m (empiricalCauseData W n ω) (none, j))
              (ŵ n ω) (ĉ n ω) n})
          atTop (𝓝 (stdGaussian (EuclideanSpace ℝ (Cell k r)) {z | weightedSup w (Y z) ≤ c})) := by
  obtain ⟨Y, hYg, hYlaw, hconv⟩ :=
    tendstoInDistribution_estimator_indepCauseLaw pTJ pC hind hlaw m hm
  let L : (Coord k r m → ℝ) →L[ℝ] ({j : Fin k // j ≤ m} → ℝ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (none, j)
  have : Nonempty {j : Fin k // j ≤ m} := ⟨⟨m, le_rfl⟩⟩
  refine ⟨fun z => L (Y z), hYg.map L, fun s => ?_, fun hw hŵ hŵm hĉ hĉm hatom => ?_⟩
  · have hsum : ∀ v : Coord k r m → ℝ,
        ∑ a, (a.1.elim (s a.2) fun _ => 0) * v a = ∑ j, s j * v (none, j) := fun v => by
      simp [Fintype.sum_prod_type, Fintype.sum_option]
    have h := hYlaw fun a => a.1.elim (s a.2) fun _ => 0
    simp only [hsum] at h
    exact h
  · exact tendsto_coverage_simultaneousBand (hconv.continuous_comp L.continuous) hw hŵ hŵm hĉ hĉm
      hatom

end KaplanMeier

end MathlibExt.Probability.Statistics.SimultaneousBands

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.TajimaD
public import MathlibExt.Biology.PopulationGenetics.Coalescent.TajimaVariance
public import MathlibExt.Probability.Statistics.Slutsky
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Normalized Tajima's `D`: mean, delta-method variance and asymptotic normality

Tajima's `D = N / √V` (`tajimaD`) divides the numerator `N = π - S / a₁` by the square root of
the unbiased estimator `V = e₁ S + e₂ S (S - 1)` of `Var N = c₁ θ + c₂ θ²`
(`KingmanTimes.variance_tajimaNumerator`, `KingmanTimes.integral_tajimaVarEstimator`).
Tajima (1989) treats `D` as approximately standardized: mean about `0`, variance about `1`.
This file makes the three parts of that statement precise.

* **The mean is not `0` in general.** `E[N] = 0` (`KingmanTimes.integral_tajimaNumerator`), but
  `E[N / √V]` is not `E[N] / E[√V]`: `D` is a ratio of dependent random variables. Exactly,
  `E[D] = Cov(N, 1/√V) + E[N] E[1/√V]`, so under the neutral model `E[D] = Cov(N, 1/√V)`
  (`integral_tajimaD_eq`, `KingmanTimes.integral_tajimaD_eq_covariance`; since `P(S = 0) > 0`
  under the neutral model, `D` there means Lean's value `0` on `S = 0`, so `E[D]` is
  `E[D; S ≥ 1]`), and this covariance
  need not vanish: `exists_integral_tajimaD_ne` exhibits a two-point law of realizable data for
  `n = 4` genes with `E[N] = 0` and `E[D] > 0`.
* **Delta-method variance.** The map `(x, y) ↦ x / √y` has derivative
  `(1 / √y₀, -x₀ / (2 y₀ √y₀))` at `(x₀, y₀)`, `y₀ > 0` (`hasFDerivAt_div_sqrt`); at `x₀ = 0` the
  fluctuation of the denominator drops out to first order (`hasFDerivAt_div_sqrt_zero`). The
  linearization of `D` at `(E N, E V) = (0, c₁ θ + c₂ θ²)` therefore has variance
  `Var N / (c₁ θ + c₂ θ²) = 1` (`variance_linearization_div_sqrt`,
  `KingmanTimes.variance_tajimaD_linearization_eq_one`, which reuses Tajima's variance identity
  from `Coalescent/TajimaVariance.lean`).
* **Asymptotic normality conditions.** If along some asymptotic regime the scaled numerator
  satisfies a central limit theorem `r_k N_k →ᵈ N(0, σ²)` and the variance estimator is
  ratio-consistent, `r_k² V_k → σ² > 0` in probability, then `D_k →ᵈ N(0, 1)`
  (`tendstoInDistribution_tajimaD_gaussian`, Slutsky's theorem). At a fixed sample size `n` the
  two conditions cannot hold simultaneously for data obeying the real-data bound `|N| ≤ β S`
  (with `β` depending only on `n`): together they would give `D_k →ᵈ N(0, 1)`, but the bound
  makes `|D_k| ≤ β / √(min(e₁, e₂) / 2)` for every `k` (`abs_tajimaD_le` where `S_k ≥ 1`; Lean's
  value `D_k = 0` where `S_k = 0`), and a limit in distribution of laws supported in one bounded
  closed interval is supported in that interval, so it is not `N(0, 1)`. This limit argument is
  not formalized here.
  `not_hasLaw_tajimaD_gaussianReal` proves only the single-sample statement: under the same bound
  the law of `D` is not exactly Gaussian. This is why Tajima fitted a beta distribution instead.

## Main results

* `integral_tajimaD_eq`: `E[D] = Cov(N, 1/√V) + E[N] E[1/√V]`.
* `inv_sqrt_tajimaVarEstimator_le`, `memLp_inv_sqrt_tajimaVarEstimator`: `1/√V ≤ 1/√e₁` on
  integer-valued data, so `1/√V` has all moments.
* `KingmanTimes.integral_tajimaD_eq_covariance`: under the neutral model, `E[D] = Cov(N, 1/√V)`.
* `exists_integral_tajimaD_ne`: `E[N] = 0` but `E[D] ≠ E[N] / E[√V]`, indeed `E[D] > 0`.
* `hasFDerivAt_div_sqrt`, `hasFDerivAt_div_sqrt_zero`: the derivative of `(x, y) ↦ x / √y`.
* `variance_linearization_div_sqrt`, `KingmanTimes.variance_tajimaD_linearization_eq_one`: the
  delta-method variance of `D` is `1`.
* `tendstoInDistribution_tajimaD_gaussian`: conditions for `D_k →ᵈ N(0, 1)`.
* `abs_tajimaD_le`, `not_hasLaw_tajimaD_gaussianReal`: for fixed `n`, `D` is bounded and its law
  is not exactly Gaussian.

## References

* F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA
  polymorphism*, Genetics 123 (1989), 585–595.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 3.1 (delta method) and
  Lemma 2.8 (Slutsky).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-! ### Positivity of Tajima's constants -/

private theorem tajimaA1_pos {n : ℕ} (hn : 2 ≤ n) : 0 < tajimaA1 n := by
  rw [tajimaA1_eq_harmonic]
  exact_mod_cast harmonic_pos (by omega)

private theorem tajimaE1_pos {n : ℕ} (hn : 4 ≤ n) : 0 < tajimaE1 n := by
  simpa using tajimaVarEstimator_pos hn (S := 1) le_rfl

private theorem tajimaE2_pos {n : ℕ} (hn : 4 ≤ n) : 0 < tajimaE2 n := by
  have ha2 : 0 ≤ tajimaA2 n := sum_nonneg fun i _ => by positivity
  have := tajimaA1_pos (n := n) (by omega)
  exact div_pos (tajimaC2_pos hn) (by positivity)

/-- `Var(π - S / a₁) = c₁ θ + c₂ θ²` is positive for `n ≥ 4` and `θ > 0`. -/
theorem tajimaVariance_pos {n : ℕ} (hn : 4 ≤ n) {θ : ℝ} (hθ : 0 < θ) :
    0 < tajimaC1 n * θ + tajimaC2 n * θ ^ 2 := by
  have := tajimaC1_pos hn
  have := tajimaC2_pos hn
  positivity

/-! ### The mean of `D` -/

section Mean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The mean of Tajima's `D`**: with `N = π - S / a₁` and `R = 1 / √(e₁ S + e₂ S (S - 1))`,
`E[D] = Cov(N, R) + E[N] E[R]` whenever `N` and `R` are square integrable. In particular
`E[D] = 0` iff `Cov(N, R) = -E[N] E[R]`; under the neutral model `E[N] = 0`, so `E[D]` is the
covariance of the numerator with the reciprocal denominator. -/
theorem integral_tajimaD_eq [IsProbabilityMeasure μ] {n : ℕ} {π S : Ω → ℝ}
    (hN : MemLp (fun ω => π ω - S ω / tajimaA1 n) 2 μ)
    (hR : MemLp (fun ω => (Real.sqrt (tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1))))⁻¹)
      2 μ) :
    μ[fun ω => tajimaD n (π ω) (S ω)] =
      cov[fun ω => π ω - S ω / tajimaA1 n,
        fun ω => (Real.sqrt (tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1))))⁻¹; μ] +
      μ[fun ω => π ω - S ω / tajimaA1 n] *
        μ[fun ω => (Real.sqrt (tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1))))⁻¹] := by
  rw [covariance_eq_sub hN hR, sub_add_cancel]
  simp only [tajimaD, div_eq_mul_inv]
  rfl

/-- On integer-valued data (`S = 0` or `S ≥ 1`) and for `n ≥ 4`, the reciprocal denominator of
`D` is bounded: `1 / √(e₁ S + e₂ S (S - 1)) ≤ 1 / √e₁`. (At `S = 0` the left side is Lean's
junk value `1 / √0 = 0`.) -/
theorem inv_sqrt_tajimaVarEstimator_le {n : ℕ} (hn : 4 ≤ n) {S : ℝ} (hS : S = 0 ∨ 1 ≤ S) :
    (Real.sqrt (tajimaE1 n * S + tajimaE2 n * (S * (S - 1))))⁻¹ ≤ (Real.sqrt (tajimaE1 n))⁻¹ := by
  have he1 := tajimaE1_pos hn
  have he2 := tajimaE2_pos hn
  rcases hS with rfl | hS
  · simp
  · refine inv_anti₀ (Real.sqrt_pos.2 he1) (Real.sqrt_le_sqrt ?_)
    have : 0 ≤ tajimaE2 n * (S * (S - 1)) :=
      mul_nonneg he2.le (mul_nonneg (by linarith) (by linarith))
    nlinarith

/-- On integer-valued data and for `n ≥ 4`, the reciprocal denominator of `D` lies in every
`Lᵖ` of a finite measure. -/
theorem memLp_inv_sqrt_tajimaVarEstimator [IsFiniteMeasure μ] {n : ℕ} (hn : 4 ≤ n)
    {S : Ω → ℝ} (hSm : AEMeasurable S μ) (hS : ∀ᵐ ω ∂μ, S ω = 0 ∨ 1 ≤ S ω)
    (p : ENNReal) :
    MemLp (fun ω => (Real.sqrt (tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1))))⁻¹) p μ := by
  refine MemLp.of_bound (by fun_prop) (Real.sqrt (tajimaE1 n))⁻¹ ?_
  filter_upwards [hS] with ω hω
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_sqrt_tajimaVarEstimator_le hn hω

namespace KingmanTimes

/-- **The mean of Tajima's `D` under the neutral model** is the covariance of the numerator
`N = π - S / a₁` with the reciprocal denominator `1 / √(e₁ S + e₂ S (S - 1))`, for `n ≥ 4` genes
and integer-valued `S`, under the hypotheses of `KingmanTimes.integral_tajimaNumerator` (which
gives `E[N] = 0`). Whether this covariance vanishes is a property of the joint law of `(π, S)`,
not of the first two moments of `N`; see `exists_integral_tajimaD_ne`.

Under the neutral model `S = 0` has positive probability, and there `D` takes Lean's junk value
`N / √0 = 0` (Tajima's `D` is undefined), so the left side is `E[D; S ≥ 1]`, the mean of `D` over
samples with at least one segregating site, with `D := 0` on `S = 0`. -/
theorem integral_tajimaD_eq_covariance {n : ℕ} (K : KingmanTimes μ n) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {S : Ω → ℝ} {D τ : Finset (Fin n) → Ω → ℝ} {θ : ℝ}
    (hn : 4 ≤ n) (hS2 : MemLp S 2 μ) (hSnat : ∀ᵐ ω ∂μ, S ω = 0 ∨ 1 ≤ S ω)
    (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hτ : ∀ s ∈ samplePairs n, HasLaw (τ s) (expMeasure 1) μ)
    (hD2 : ∀ s ∈ samplePairs n, MemLp (D s) 2 μ)
    (hD : ∀ s ∈ samplePairs n, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω) :
    μ[fun ω => tajimaD n (meanPairDiff n D ω) (S ω)] =
      cov[fun ω => meanPairDiff n D ω - S ω / tajimaA1 n,
        fun ω => (Real.sqrt (tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1))))⁻¹; μ] := by
  have hπ : MemLp (meanPairDiff n D) 2 μ := (memLp_finsetSum (samplePairs n) hD2).const_mul _
  have hN : MemLp (fun ω => meanPairDiff n D ω - S ω / tajimaA1 n) 2 μ :=
    hπ.sub (by simpa [div_eq_mul_inv, mul_comm] using hS2.const_mul (tajimaA1 n)⁻¹)
  rw [integral_tajimaD_eq hN
    (memLp_inv_sqrt_tajimaVarEstimator hn hS2.aestronglyMeasurable.aemeasurable hSnat 2),
    K.integral_tajimaNumerator hm (by omega) (hS2.integrable one_le_two) hS hτ
      (fun s hs => (hD2 s hs).integrable one_le_two) hD, zero_mul, add_zero]

end KingmanTimes

end Mean

/-! ### `E[D] ≠ 0`: a counterexample -/

/-- **`E[D] ≠ E[N] / E[√V]`**: a law of data for `n = 4` genes under which Tajima's numerator
`N = π - S / a₁` has mean `0` while `D = N / √V` has positive mean. The two outcomes are
realizable data sets: one doubleton site (`S = 1`, `π = 2 · 2 / 6 = 2/3`) with probability `3/7`,
and two singleton sites (`S = 2`, `π = 2 · 3 / 6 = 1`) with probability `4/7`. Here
`N = 4/33` and `N = -1/11` respectively, so `E[N] = 0`, but the negative value of `N` is divided
by the larger denominator. The law is not that of the neutral coalescent; the point is that
`E[N] = 0` (the conclusion of `KingmanTimes.integral_tajimaNumerator`) does not by itself force
`E[D] = 0`. -/
theorem exists_integral_tajimaD_ne :
    ∃ (μ : Measure Bool) (π S : Bool → ℝ), IsProbabilityMeasure μ ∧
      (∀ b, S b = 1 ∨ S b = 2) ∧
      μ[fun b => π b - S b / tajimaA1 4] = 0 ∧
      μ[fun b => tajimaD 4 (π b) (S b)] ≠
        μ[fun b => π b - S b / tajimaA1 4] /
          μ[fun b => Real.sqrt (tajimaE1 4 * S b + tajimaE2 4 * (S b * (S b - 1)))] ∧
      0 < μ[fun b => tajimaD 4 (π b) (S b)] := by
  set μ : Measure Bool :=
    (3 / 7 : NNReal) • Measure.dirac true + (4 / 7 : NNReal) • Measure.dirac false with hμ
  have hint : ∀ f : Bool → ℝ, ∫ b, f b ∂μ = 3 / 7 * f true + 4 / 7 * f false := by
    intro f
    rw [hμ, integral_add_measure Integrable.of_finite Integrable.of_finite,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_dirac, integral_dirac]
    simp [NNReal.smul_def]
  have ha : tajimaA1 4 = 11 / 6 := by
    simp [tajimaA1, sum_Ico_succ_top]
    norm_num
  have he1 := tajimaE1_pos (n := 4) le_rfl
  have he2 := tajimaE2_pos (n := 4) le_rfl
  have hu : 0 < Real.sqrt (tajimaE1 4) := Real.sqrt_pos.2 he1
  have huw : Real.sqrt (tajimaE1 4) < Real.sqrt (tajimaE1 4 * 2 + tajimaE2 4 * 2) :=
    Real.sqrt_lt_sqrt he1.le (by linarith)
  have hmean : ∫ b, (fun b : Bool => (if b then (2 / 3 : ℝ) else 1) -
      (if b then (1 : ℝ) else 2) / tajimaA1 4) b ∂μ = 0 := by
    rw [hint]
    simp only [ite_true, Bool.false_eq_true, ite_false, ha]
    norm_num
  have hpos : 0 < ∫ b, (fun b : Bool => tajimaD 4 (if b then (2 / 3 : ℝ) else 1)
      (if b then (1 : ℝ) else 2)) b ∂μ := by
    rw [hint]
    simp only [ite_true, Bool.false_eq_true, ite_false, tajimaD, ha]
    have key : 12 / 231 / Real.sqrt (tajimaE1 4 * 2 + tajimaE2 4 * 2) <
        12 / 231 / Real.sqrt (tajimaE1 4) := div_lt_div_of_pos_left (by norm_num) hu huw
    have e : 3 / 7 * ((2 / 3 - 1 / (11 / 6)) /
          Real.sqrt (tajimaE1 4 * 1 + tajimaE2 4 * (1 * (1 - 1)))) +
        4 / 7 * ((1 - 2 / (11 / 6)) / Real.sqrt (tajimaE1 4 * 2 + tajimaE2 4 * (2 * (2 - 1)))) =
        12 / 231 / Real.sqrt (tajimaE1 4) -
          12 / 231 / Real.sqrt (tajimaE1 4 * 2 + tajimaE2 4 * 2) := by
      norm_num
      ring
    rw [e]
    linarith
  refine ⟨μ, fun b => if b then 2 / 3 else 1, fun b => if b then 1 else 2, ?_,
    fun b => by cases b <;> simp, hmean, ?_, hpos⟩
  · constructor
    rw [hμ]
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ]
    rw [← ENNReal.coe_one, ENNReal.smul_def, ENNReal.smul_def]
    simp only [smul_eq_mul]
    norm_cast
    norm_num
  · rw [hmean, zero_div]
    exact hpos.ne'

/-! ### Delta-method variance -/

/-- **Derivative of the studentizing map** `(x, y) ↦ x / √y` at `(x₀, y₀)` with `y₀ > 0`:
`dx / √y₀ - x₀ dy / (2 y₀ √y₀)`. -/
theorem hasFDerivAt_div_sqrt {x₀ y₀ : ℝ} (hy : 0 < y₀) :
    HasFDerivAt (fun p : ℝ × ℝ => p.1 / Real.sqrt p.2)
      ((Real.sqrt y₀)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ -
        (x₀ / (2 * y₀ * Real.sqrt y₀)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (x₀, y₀) := by
  have hs : 0 < Real.sqrt y₀ := Real.sqrt_pos.2 hy
  have h1 : HasDerivAt (fun y => (Real.sqrt y)⁻¹)
      (-(1 / (2 * Real.sqrt y₀)) / Real.sqrt y₀ ^ 2) y₀ :=
    (Real.hasDerivAt_sqrt hy.ne').inv hs.ne'
  have h2 := h1.comp_hasFDerivAt (f := Prod.snd) (x₀, y₀) (hasFDerivAt_snd (𝕜 := ℝ))
  have h3 := (hasFDerivAt_fst (p := (x₀, y₀))).mul h2
  convert h3 using 1
  · funext p
    simp [div_eq_mul_inv]
  · refine ContinuousLinearMap.ext fun p => ?_
    simp only [sub_apply, add_apply,
      smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Function.comp_apply, smul_eq_mul, Real.sq_sqrt hy.le]
    field_simp
    ring

/-- At a point with zero numerator, `(x, y) ↦ x / √y` has derivative `dx / √y₀`: to first order
the fluctuation of the denominator does not affect the studentized statistic. -/
theorem hasFDerivAt_div_sqrt_zero {y₀ : ℝ} (hy : 0 < y₀) :
    HasFDerivAt (fun p : ℝ × ℝ => p.1 / Real.sqrt p.2)
      ((Real.sqrt y₀)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ) (0, y₀) := by
  simpa using hasFDerivAt_div_sqrt (x₀ := 0) hy

/-- **Delta-method variance of a studentized statistic**: the linearization
`(√v)⁻¹ (N - 0) + 0 · (V - v)` of `N / √V` at `(0, v)`, `v > 0` (`hasFDerivAt_div_sqrt_zero`), has
variance `Var N / v`. -/
theorem variance_linearization_div_sqrt {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (N V : Ω → ℝ) {v : ℝ} (hv : 0 < v) :
    Var[fun ω => ((Real.sqrt v)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ) (N ω, V ω - v); μ] =
      Var[N; μ] / v := by
  simp only [smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
  rw [variance_const_mul, inv_pow, Real.sq_sqrt hv.le, inv_mul_eq_div]

namespace KingmanTimes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ} (K : KingmanTimes μ n)

/-- **The delta-method variance of Tajima's `D` is `1`** under the neutral model, for `n ≥ 4`
genes and `θ > 0`, under the hypotheses of Tajima's variance identity
`KingmanTimes.variance_tajimaNumerator`. With `N = π - S / a₁`, `V = e₁ S + e₂ S (S - 1)` and
`v = c₁ θ + c₂ θ²`: the map `(x, y) ↦ x / √y` has derivative `L = (√v)⁻¹ • fst` at the mean point
`(E N, E V) = (0, v)`, and the linearization `L (N - E N, V - E V)` has variance `1`. -/
theorem variance_tajimaD_linearization_eq_one [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {S : Ω → ℝ} {D τ : Finset (Fin n) → Ω → ℝ}
    {ℓ : Finset (Fin n) → Finset (Fin n) → Ω → ℝ} {θ : ℝ} (hn : 4 ≤ n) (hθ : 0 < θ)
    (hS2 : MemLp S 2 μ) (hS : μ[S | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hSvar : Var[S; μ | m] =ᵐ[μ] fun ω => θ / 2 * K.totalLength ω)
    (hτ : ∀ s ∈ samplePairs n, HasLaw (τ s) (expMeasure 1) μ)
    (hτ₁ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, #(s ∩ t) = 1 →
      μ[fun ω => τ s ω * τ t ω] = 4 / 3)
    (hτ₀ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, Disjoint s t →
      μ[fun ω => τ s ω * τ t ω] = 11 / 9)
    (hτL : ∀ s ∈ samplePairs n,
      μ[fun ω => τ s ω * K.totalLength ω] = 2 * tajimaA1 n + ((n : ℝ) + 2) / n)
    (hℓ₂ : ∀ s ∈ samplePairs n, ℓ s s =ᵐ[μ] fun ω => 2 * τ s ω)
    (hℓ₁ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, #(s ∩ t) = 1 →
      ℓ s t =ᵐ[μ] fun ω => τ s ω + τ t ω - τ (symmDiff s t) ω)
    (hℓ₀ : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n, Disjoint s t → μ[ℓ s t] = 2 / 3)
    (hD2 : ∀ s ∈ samplePairs n, MemLp (D s) 2 μ)
    (hD : ∀ s ∈ samplePairs n, μ[D s | m] =ᵐ[μ] fun ω => θ * τ s ω)
    (hDD : ∀ s ∈ samplePairs n, ∀ t ∈ samplePairs n,
      μ[fun ω => D s ω * D t ω | m] =ᵐ[μ]
        fun ω => θ ^ 2 * (τ s ω * τ t ω) + θ / 2 * ℓ s t ω)
    (hDS : ∀ s ∈ samplePairs n, μ[fun ω => D s ω * S ω | m] =ᵐ[μ]
      fun ω => θ ^ 2 / 2 * (τ s ω * K.totalLength ω) + θ * τ s ω) :
    HasFDerivAt (fun p : ℝ × ℝ => p.1 / Real.sqrt p.2)
        ((Real.sqrt (tajimaC1 n * θ + tajimaC2 n * θ ^ 2))⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (μ[fun ω => meanPairDiff n D ω - S ω / tajimaA1 n],
          μ[fun ω => tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1))]) ∧
      Var[fun ω => ((Real.sqrt (tajimaC1 n * θ + tajimaC2 n * θ ^ 2))⁻¹ •
          ContinuousLinearMap.fst ℝ ℝ ℝ)
        (meanPairDiff n D ω - S ω / tajimaA1 n -
            μ[fun ω => meanPairDiff n D ω - S ω / tajimaA1 n],
          tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1)) -
            μ[fun ω => tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1))]); μ] = 1 := by
  have hv := tajimaVariance_pos hn hθ
  have hEN := K.integral_tajimaNumerator hm (by omega) (hS2.integrable one_le_two) hS hτ
    (fun s hs => (hD2 s hs).integrable one_le_two) hD
  have hEV := K.integral_tajimaVarEstimator hm (by omega) hS2 hS hSvar
  have hVN := K.variance_tajimaNumerator hm (by omega) hS2 hS hSvar hτ hτ₁ hτ₀ hτL hℓ₂ hℓ₁ hℓ₀
    hD2 hD hDD hDS
  rw [hEN, hEV]
  refine ⟨hasFDerivAt_div_sqrt_zero hv, ?_⟩
  have h := variance_linearization_div_sqrt μ (fun ω => meanPairDiff n D ω - S ω / tajimaA1 n)
    (fun ω => tajimaE1 n * S ω + tajimaE2 n * (S ω * (S ω - 1))) hv
  simp only [sub_zero]
  rw [h, hVN, div_self hv.ne']

end KingmanTimes

/-! ### Asymptotic normality: sufficient conditions, and non-Gaussianity at fixed `n` -/

/-- **Conditions for asymptotic normality of Tajima's `D`.** Along a filter `l` (an asymptotic
regime, e.g. a growing number of independent loci), let the `k`-th data set have `n k` genes,
pairwise-difference mean `π k` and `S k` segregating sites, and let `r k > 0` be scalings. If

* the scaled numerator satisfies a central limit theorem,
  `r k (π k - S k / a₁) →ᵈ N(0, σ²)`, and
* the variance estimator is ratio-consistent at the same scale,
  `r k² (e₁ S k + e₂ S k (S k - 1)) → σ²` in probability, with `σ² > 0`,

then `D k →ᵈ N(0, 1)` (Slutsky's theorem). The conclusion is stated for any random variable `W`
with the standard Gaussian law. -/
theorem tendstoInDistribution_tajimaD_gaussian {ι Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P'] {l : Filter ι} [l.IsCountablyGenerated] {n : ι → ℕ}
    {π S : ι → Ω → ℝ} {r : ι → ℝ} {Z W : Ω' → ℝ} {σ2 : NNReal} (hσ : σ2 ≠ 0)
    (hr : ∀ k, 0 < r k)
    (hN : TendstoInDistribution (fun k ω => r k * (π k ω - S k ω / tajimaA1 (n k))) l Z
      (fun _ => μ) P')
    (hZ : HasLaw Z (gaussianReal 0 σ2) P')
    (hV : TendstoInMeasure μ (fun k ω => r k ^ 2 *
      (tajimaE1 (n k) * S k ω + tajimaE2 (n k) * (S k ω * (S k ω - 1)))) l
      (fun _ => (σ2 : ℝ)))
    (hSm : ∀ k, AEMeasurable (S k) μ) (hW : HasLaw W (gaussianReal 0 1) P') :
    TendstoInDistribution (fun k ω => tajimaD (n k) (π k ω) (S k ω)) l W (fun _ => μ) P' := by
  have hσ' : (0 : ℝ) < σ2 := lt_of_le_of_ne σ2.2 (by exact_mod_cast hσ.symm)
  have hs : 0 < Real.sqrt σ2 := Real.sqrt_pos.2 hσ'
  have hY := hV.comp_const_of_continuousAt Real.continuous_sqrt.continuousAt
  have hYm : ∀ k, AEMeasurable (fun ω => Real.sqrt (r k ^ 2 *
      (tajimaE1 (n k) * S k ω + tajimaE2 (n k) * (S k ω * (S k ω - 1))))) μ := fun k => by
    have := hSm k
    fun_prop
  have h := hN.div_of_tendstoInMeasure_const hs.ne' hY hYm
  have hlaw : HasLaw (fun ω => Z ω / Real.sqrt σ2) (gaussianReal 0 1) P' := by
    have h' := gaussianReal_mul_const hZ (Real.sqrt σ2)⁻¹
    simp only [mul_zero, ← div_eq_mul_inv] at h'
    convert h' using 2
    ext
    simp only [NNReal.coe_one, NNReal.coe_mul, NNReal.coe_mk, inv_pow, Real.sq_sqrt hσ'.le]
    field_simp
  refine (h.congr_hasLaw hlaw hW).congr (fun k => ae_of_all _ fun ω => ?_)
    (ae_of_all _ fun _ => rfl)
  simp only [tajimaD]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hr k).le, mul_div_mul_left _ _ (hr k).ne']

/-- **`D` has bounded range for a fixed sample size**: for `n ≥ 4`, `S ≥ 1` and
`|π - S / a₁| ≤ β S`, `|D| ≤ β / √(min(e₁, e₂) / 2)`. For real data the hypothesis holds with
`β = max(n / (2 (n - 1)), 1 / a₁)`, since each segregating site contributes between `0` and
`n / (2 (n - 1))` to `π`. -/
theorem abs_tajimaD_le {n : ℕ} (hn : 4 ≤ n) {π S β : ℝ} (hS : 1 ≤ S)
    (hN : |π - S / tajimaA1 n| ≤ β * S) :
    |tajimaD n π S| ≤ β / Real.sqrt (min (tajimaE1 n) (tajimaE2 n) / 2) := by
  have he1 := tajimaE1_pos hn
  have he2 := tajimaE2_pos hn
  set c := min (tajimaE1 n) (tajimaE2 n) / 2 with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ tajimaE1 n / 2 := by rw [hc]; gcongr; exact min_le_left _ _
  have hc2 : c ≤ tajimaE2 n / 2 := by rw [hc]; gcongr; exact min_le_right _ _
  have hV : c * S ^ 2 ≤ tajimaE1 n * S + tajimaE2 n * (S * (S - 1)) := by
    rcases le_total S 2 with h2 | h2
    · have : 0 ≤ tajimaE2 n * (S * (S - 1)) :=
        mul_nonneg he2.le (mul_nonneg (by linarith) (by linarith))
      nlinarith [mul_le_mul_of_nonneg_right hc1 (sq_nonneg S),
        mul_nonneg (mul_nonneg he1.le (by linarith : (0 : ℝ) ≤ S)) (by linarith : (0 : ℝ) ≤ 2 - S)]
    · have : 0 ≤ tajimaE1 n * S := mul_nonneg he1.le (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg S),
        mul_nonneg (mul_nonneg he2.le (by linarith : (0 : ℝ) ≤ S)) (by linarith : (0 : ℝ) ≤ S - 2)]
  have hsq : Real.sqrt c * S ≤ Real.sqrt (tajimaE1 n * S + tajimaE2 n * (S * (S - 1))) := by
    calc Real.sqrt c * S = Real.sqrt (c * S ^ 2) := by
          rw [Real.sqrt_mul hc0.le, Real.sqrt_sq (by linarith)]
      _ ≤ _ := Real.sqrt_le_sqrt hV
  have hcS : 0 < Real.sqrt c * S := mul_pos (Real.sqrt_pos.2 hc0) (by linarith)
  rw [tajimaD, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc |π - S / tajimaA1 n| / Real.sqrt (tajimaE1 n * S + tajimaE2 n * (S * (S - 1)))
      ≤ β * S / (Real.sqrt c * S) := div_le_div₀ ((abs_nonneg _).trans hN) hN hcS hsq
    _ = β / Real.sqrt c := mul_div_mul_right _ _ (by linarith)

/-- **`D` is not Gaussian for a fixed sample size**: for `n ≥ 4` genes, integer-valued `S` and
`|π - S / a₁| ≤ β S` almost surely, `D` is almost surely bounded (`abs_tajimaD_le`; at `S = 0`
it takes the junk value `0`), so its law is not `N(m, v)` for any `v ≠ 0`. This is a statement
about one fixed sample; it does not by itself rule out a Gaussian limit in distribution of a
sequence of such samples (see the module docstring). -/
theorem not_hasLaw_tajimaD_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : ℕ} (hn : 4 ≤ n) {π S : Ω → ℝ} {β : ℝ} (hS : ∀ᵐ ω ∂μ, S ω = 0 ∨ 1 ≤ S ω)
    (hN : ∀ᵐ ω ∂μ, |π ω - S ω / tajimaA1 n| ≤ β * S ω) (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    ¬ HasLaw (fun ω => tajimaD n (π ω) (S ω)) (gaussianReal m v) μ := by
  intro hlaw
  set M := |β| / Real.sqrt (min (tajimaE1 n) (tajimaE2 n) / 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hb : ∀ᵐ ω ∂μ, |tajimaD n (π ω) (S ω)| ≤ M := by
    filter_upwards [hS, hN] with ω hS hN
    rcases hS with h0 | h1
    · simp [tajimaD, h0, hM0]
    · exact (abs_tajimaD_le hn h1 hN).trans
        (div_le_div_of_nonneg_right (le_abs_self β) (Real.sqrt_nonneg _))
  have h0 : μ {ω | ¬ |tajimaD n (π ω) (S ω)| ≤ M} = 0 := ae_iff.1 hb
  rw [hlaw.measure_eq (p := fun x => ¬ |x| ≤ M)
    (measurableSet_le (f := fun x : ℝ => |x|) (g := fun _ => M) (by fun_prop)
      (by fun_prop)).compl] at h0
  have hvol := gaussianReal_absolutelyContinuous' m hv h0
  have hsub : Set.Ioi M ⊆ {x : ℝ | ¬ |x| ≤ M} := fun x hx => by
    simp only [Set.mem_ofPred_eq, not_le]
    exact lt_of_lt_of_le hx (le_abs_self x)
  have := measure_mono_null hsub hvol
  simp at this

end MathlibExt.Biology.PopulationGenetics.Coalescent

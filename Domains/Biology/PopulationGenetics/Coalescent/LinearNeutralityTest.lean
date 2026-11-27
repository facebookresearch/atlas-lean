/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.SFSCovariance
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.SumIntegralComparisons

/-!
# General linear neutrality tests and weight-consistent scaling

Let `ξ_i` (`1 ≤ i ≤ n - 1`) be the unfolded site frequency spectrum of a sample of `n`
sequences of length `L`: the number of segregating sites whose derived allele is carried by
exactly `i` of the sequences. Under the standard neutral model `E ξ_i = θ L / i`, with `θ` the
scaled mutation rate per base (`SiteFrequencySpectrum.integral_sfs`, where the rate `θ L` of the
whole sequence is called `θ`). For real weights `W_i` (the `Ω_i` of the sources) with
`∑_{i=1}^{n-1} W_i = 0`, the **general linear neutrality test** (Achaz 2009) is

`T_W = ∑_i i W_i ξ_i / √Var(∑_j j W_j ξ_j)`,

with the variance computed under the neutral model (`linearNeutralityTest`). Following
Ramos-Onsins, Marmorini, Achaz and Ferretti (2023, Sections 1, 2.1 and 2.2):

* `T_W` has mean `0` and variance `1` under neutrality, and the centred, unit-variance linear
  statistics of the spectrum are exactly these tests;
* with `W_i = w_i - w'_i` it is the standardized difference of the two estimators
  `θ̂_w = L⁻¹ ∑_i i w_i ξ_i` and `θ̂_w'`, unbiased for `θ` when `∑_i w_i = ∑_i w'_i = 1`;
* **weight-consistent scaling**: a test should weigh each population frequency of the derived
  allele in the same way at every sample size, so its weights should follow a fixed weight
  function of the sample frequency `f = i / n`. Two centred ways of doing so are
  `centredWeights` (from a weight function `W(f)` with `∫₀¹ W = 0`) and `normalizedWeights` (from
  the weight functions `w(f)`, `w'(f)` of two estimators, with `∫₀¹ w = ∫₀¹ w' = 1`). Up to a
  positive factor, which does not change the test, both are within `O(1 / n)` of the weight
  function at `i / n`, and so of each other when `W = w - w'`, if the weight functions have
  bounded variation on `[0, 1]`;
* the normalized form does not change when a weight function is multiplied by a nonzero
  constant, such as the normalization `1 / log N` of Watterson's weight function `1 / (f log N)`,
  which diverges at `f = 0` and is cut off at the inverse population size `1 / N`;
* Fay and Wu's `H` is the test of `w(f) = 1` and `w'(f) = 2 f`, and of `W(f) = 1 - 2 f`.

## Main definitions

* `linearNeutralityTest μ n W ξ`: the test `T_W`, with the variance taken under `μ`.
* `centredWeights W n`: the weights `W(i / n) - (n - 1)⁻¹ ∑_{j=1}^{n-1} W(j / n)`.
* `normalizedWeights w w' n`: the weights
  `w(i / n) / ∑_{j=1}^{n-1} w(j / n) - w'(i / n) / ∑_{j=1}^{n-1} w'(j / n)`.

## Main results

* `integral_linearNeutralityTest`, `integral_linearNeutralityTest_kingman`: `E T_W = 0`.
* `variance_linearNeutralityTest`, `variance_linearNeutralityTest_kingman`: `Var T_W = 1`.
* `exists_linearNeutralityTest_eq_iff`: a linear statistic of the spectrum has mean `0` and
  variance `1` exactly when it is a test `T_W` with `∑_i W_i = 0`.
* `linearNeutralityTest_const_mul`: weights rescaled by a factor `c > 0` give the same test.
* `integral_thetaWeighted_div`, `linearNeutralityTest_sub`: the test of `w - w'` is the
  standardized difference of two unbiased estimators of `θ`.
* `sum_centredWeights`, `sum_normalizedWeights`: both forms of the weights sum to `0`.
* `exists_abs_centredWeights_sub_le`, `exists_abs_mul_normalizedWeights_sub_le`,
  `exists_abs_mul_normalizedWeights_sub_centredWeights_le`: the `O(1 / n)` bounds.
* `normalizedWeights_const_mul`, `not_exists_centredWeights_three_eq_const_mul`: the normalized
  form ignores constant factors, such as the cutoff of a divergent weight function, and the
  centred form does not.
* `linearNeutralityTest_fayWuH`: Fay and Wu's `H` in both forms.

## Implementation notes

The rate `O(1 / n)` needs some regularity of the weight functions: Ramos-Onsins et al. state it
for bounded, piecewise continuous weight functions, but the difference of the two forms is
governed by how fast the Riemann sums `n⁻¹ ∑_j w(j / n)` approach `∫₀¹ w`, and for a continuous
function they need not do so at rate `1 / n`. The bounds here assume bounded variation on
`[0, 1]`, which covers piecewise monotone weight functions with jumps. The normalized weights
are of order `1 / n`; the bounds compare them, multiplied by `n`, with the weight function and
with the centred weights, and multiplying the weights by `n` does not change the test
(`linearNeutralityTest_const_mul`).

Watterson's weight function `1 / (f log N)` is not of bounded variation on `[0, 1]`. What is
proved for it is the invariance `normalizedWeights_const_mul`, through which the cutoff `N`
drops out of the normalized weights. The centred weights of `w - c w'` have no such invariance:
for `n = 3`, `w(f) = 2 (1 - f)` (Tajima's `θ_π`) and `w'(f) = 1 / f` (Watterson's estimator), the
first of them is `1 / 3 - 3 c / 4` (`centredWeights_three_one`), whose sign depends on `c`
(`not_exists_centredWeights_three_eq_const_mul`).

## References

* G. Achaz, *Frequency spectrum neutrality tests: one for all and all for one*, Genetics 183
  (2009), 249–258.
* S. E. Ramos-Onsins, G. Marmorini, G. Achaz and L. Ferretti, *A general framework for
  neutrality tests based on the site frequency spectrum*, Genes 14 (2023), 1714, Section 1,
  Eq. (1), Sections 2.1–2.2, Eqs. (3)–(11), and Appendix A.1, Theorem A1.
* J. C. Fay and C.-I. Wu, *Hitchhiking under positive Darwinian selection*, Genetics 155
  (2000), 1405–1413.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.LinearNeutralityTest

open SiteFrequencySpectrum VariableSFS SFSCovariance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The test -/

/-- **General linear neutrality test** (Achaz 2009; Ramos-Onsins, Marmorini, Achaz and
Ferretti 2023, Eq. (3)). For a sample of `n` sequences with unfolded site frequency spectrum
`ξ i` (the number of segregating sites whose derived allele is carried by exactly `i` of the
sequences, `1 ≤ i ≤ n - 1`), real weights `W i` (the `Ω_i` of the sources) and the law `μ` of
the spectrum under the neutral model,
`T_W = ∑_{i=1}^{n-1} i W_i ξ_i / √Var_μ(∑_{j=1}^{n-1} j W_j ξ_j)`.
The numerator is the weighted sum `thetaWeighted n W ξ`. The variance in the denominator is a
number computed under `μ`, so `T_W` is a statistic of the spectrum, which can also be evaluated
under other laws of `ξ`. It is a neutrality test when `∑_{i=1}^{n-1} W_i = 0`: then under the
neutral means `E_μ ξ_i = θ L / i` it has mean `0` (`integral_linearNeutralityTest`), and it has
variance `1` under `μ` when the variance of the numerator is not `0`
(`variance_linearNeutralityTest`). With Lean's `x / 0 = 0`, `T_W = 0` when that variance is `0`,
as `Var` is by convention for an almost everywhere strongly measurable numerator that is not
square integrable. -/
def linearNeutralityTest (μ : Measure Ω) (n : ℕ) (W : ℕ → ℝ) (ξ : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => thetaWeighted n W ξ ω / √(Var[thetaWeighted n W ξ; μ])

variable {μ : Measure Ω} {n : ℕ} {ξ : ℕ → Ω → ℝ}

/-- A test whose numerator is `c X` for a constant `c > 0` is `X` standardized. -/
private lemma linearNeutralityTest_eq_of_eq_const_mul {W : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (X : Ω → ℝ) (h : thetaWeighted n W ξ = fun ω => c * X ω) :
    linearNeutralityTest μ n W ξ = fun ω => X ω / √(Var[X; μ]) := by
  funext ω
  simp only [linearNeutralityTest, h]
  rw [variance_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le,
    mul_div_mul_left _ _ hc.ne']

/-- Under the means `E ξ_i = a / i`, the mean of `∑_i i W_i ξ_i` is `a ∑_i W_i`. -/
private lemma integral_thetaWeighted_eq (hξ_int : ∀ i, Integrable (ξ i) μ) {a : ℝ}
    (hξ : ∀ i ∈ Ico 1 n, μ[ξ i] = a / i) (W : ℕ → ℝ) :
    μ[thetaWeighted n W ξ] = a * ∑ i ∈ Ico 1 n, W i := by
  unfold thetaWeighted
  rw [integral_finsetSum _ fun i _ => (hξ_int i).const_mul _, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [integral_const_mul, hξ i hi]
  have : (i : ℝ) ≠ 0 := by have := (mem_Ico.1 hi).1; positivity
  field_simp

/-- **Linear neutrality tests are centred** (Ramos-Onsins et al. 2023, Section 2.1): if each
`ξ i` is integrable with the neutral mean `E ξ_i = θ L / i` for `1 ≤ i ≤ n - 1` (sequence
length `L`, scaled mutation rate per base `θ`) and the weights sum to zero,
`∑_{i=1}^{n-1} W_i = 0`, then `E T_W = 0`. -/
theorem integral_linearNeutralityTest {W : ℕ → ℝ} (hξ_int : ∀ i, Integrable (ξ i) μ)
    {θ L : ℝ} (hξ : ∀ i ∈ Ico 1 n, μ[ξ i] = θ * L / i) (hW : ∑ i ∈ Ico 1 n, W i = 0) :
    μ[linearNeutralityTest μ n W ξ] = 0 := by
  unfold linearNeutralityTest
  rw [integral_div, integral_thetaWeighted_eq hξ_int hξ, hW, mul_zero, zero_div]

/-- **Linear neutrality tests have variance one**: if the numerator `∑_{i=1}^{n-1} i W_i ξ_i`
has nonzero variance under `μ`, then `Var_μ T_W = 1`, since the denominator of `T_W` is the
standard deviation of its numerator. -/
theorem variance_linearNeutralityTest {W : ℕ → ℝ} (h : Var[thetaWeighted n W ξ; μ] ≠ 0) :
    Var[linearNeutralityTest μ n W ξ; μ] = 1 := by
  have : linearNeutralityTest μ n W ξ =
      fun ω => thetaWeighted n W ξ ω * (√(Var[thetaWeighted n W ξ; μ]))⁻¹ :=
    funext fun _ => div_eq_mul_inv _ _
  rw [this, variance_mul_const, inv_pow, Real.sq_sqrt (variance_nonneg _ _), mul_inv_cancel₀ h]

/-- **Linear neutrality tests are centred under Kingman's coalescent**: with the hypotheses of
`SiteFrequencySpectrum.integral_sfs` (a probability measure, measurable Kingman holding times
`K.T`, an independent random-joining block-size history `τ`, measurable for the discrete
σ-algebra, and integrable counts `ξ i` whose conditional mean given the genealogy is `θ / 2`
times the length of the branches subtending `i` sequences, so that `E ξ_i = θ / i` with `θ` the
mutation rate of the whole sequence), every test with `∑_{i=1}^{n-1} W_i = 0` has mean `0`. -/
theorem integral_linearNeutralityTest_kingman [IsProbabilityMeasure μ] (K : KingmanTimes μ n)
    (hT : ∀ k, Measurable (K.T k)) {τ : Ω → List (List ℕ)}
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    {θ : ℝ} (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => K.T k ω))
    {W : ℕ → ℝ} (hW : ∑ i ∈ Ico 1 n, W i = 0) :
    μ[linearNeutralityTest μ n W ξ] = 0 :=
  integral_linearNeutralityTest hξ_int (θ := θ) (L := 1) (fun i hi => by
    rw [mul_one]
    exact integral_sfs K hT hτ hτ_law h_indep hξ_int hξ (mem_Ico.1 hi).1 (mem_Ico.1 hi).2) hW

/-- **Linear neutrality tests have variance one under Kingman's coalescent**: with the
hypotheses of `SFSCovariance.variance_thetaWeighted_kingman` (a probability measure, measurable
Kingman holding times, an independent random-joining history `τ` measurable for the discrete
σ-algebra, and counts with the first two conditional moments of independent Poisson counts,
`SFSCondMoments`), a mutation rate `θ > 0` and a weight `W_i ≠ 0` for some `1 ≤ i ≤ n - 1`, the
numerator has variance at least `θ ∑_i W_i² i > 0`, so `Var T_W = 1`. -/
theorem variance_linearNeutralityTest_kingman [IsProbabilityMeasure μ] {K : KingmanTimes μ n}
    (hT : ∀ k, Measurable (K.T k)) {τ : Ω → List (List ℕ)}
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    {θ : ℝ} (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    (hθ : 0 < θ) {W : ℕ → ℝ} (hW : ∃ i ∈ Ico 1 n, W i ≠ 0) :
    Var[linearNeutralityTest μ n W ξ; μ] = 1 := by
  refine variance_linearNeutralityTest (ne_of_gt ?_)
  rw [variance_thetaWeighted_kingman hT hτ hτ_law h_indep h]
  obtain ⟨i, hi, hWi⟩ := hW
  have hpos : 0 < ∑ j ∈ Ico 1 n, W j ^ 2 * j := by
    refine sum_pos' (fun j _ => by positivity) ⟨i, hi, ?_⟩
    have : (0 : ℝ) < i := by exact_mod_cast (mem_Ico.1 hi).1
    have : 0 < W i ^ 2 := by positivity
    positivity
  exact add_pos_of_pos_of_nonneg (mul_pos hθ hpos) (mul_nonneg (sq_nonneg _)
    (variance_nonneg _ _))

/-- **The centred, unit-variance linear statistics of the spectrum are the tests `T_W`**
(Ramos-Onsins et al. 2023, Section 2.1). Let each `ξ i` be integrable with the neutral mean
`E_μ ξ_i = θ L / i` for `1 ≤ i ≤ n - 1`, where `θ L ≠ 0`. A linear statistic
`∑_{i=1}^{n-1} a_i ξ_i` is a test `T_W` with weights summing to `0` (and a numerator of nonzero
variance) exactly when it has mean `0` and variance `1` under `μ`; the weights are then
`W_i = a_i / i`. -/
theorem exists_linearNeutralityTest_eq_iff (hξ_int : ∀ i, Integrable (ξ i) μ) {θ L : ℝ}
    (hθL : θ * L ≠ 0) (hξ : ∀ i ∈ Ico 1 n, μ[ξ i] = θ * L / i) (a : ℕ → ℝ) :
    (∃ W : ℕ → ℝ, ∑ i ∈ Ico 1 n, W i = 0 ∧ Var[thetaWeighted n W ξ; μ] ≠ 0 ∧
        linearNeutralityTest μ n W ξ = fun ω => ∑ i ∈ Ico 1 n, a i * ξ i ω) ↔
      μ[fun ω => ∑ i ∈ Ico 1 n, a i * ξ i ω] = 0 ∧
        Var[fun ω => ∑ i ∈ Ico 1 n, a i * ξ i ω; μ] = 1 := by
  constructor
  · rintro ⟨W, hW, hV, h⟩
    rw [← h]
    exact ⟨integral_linearNeutralityTest hξ_int hξ hW, variance_linearNeutralityTest hV⟩
  · rintro ⟨h0, h1⟩
    have hS : thetaWeighted n (fun i => a i / i) ξ = fun ω => ∑ i ∈ Ico 1 n, a i * ξ i ω := by
      funext ω
      refine sum_congr rfl fun i hi => ?_
      have : (i : ℝ) ≠ 0 := by have := (mem_Ico.1 hi).1; positivity
      field_simp
    refine ⟨fun i => a i / i, ?_, ?_, ?_⟩
    · have := integral_thetaWeighted_eq hξ_int hξ (fun i => a i / i)
      rw [hS, h0] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hθL
    · rw [hS, h1]
      exact one_ne_zero
    · funext ω
      simp only [linearNeutralityTest, hS, h1, Real.sqrt_one, div_one]

/-- **Rescaling the weights** (Ramos-Onsins et al. 2023, Theorem A1): multiplying every weight
by a common factor `c > 0` does not change the test. -/
theorem linearNeutralityTest_const_mul {c : ℝ} (hc : 0 < c) (W : ℕ → ℝ) :
    linearNeutralityTest μ n (fun i => c * W i) ξ = linearNeutralityTest μ n W ξ := by
  refine linearNeutralityTest_eq_of_eq_const_mul hc (thetaWeighted n W ξ) ?_
  funext ω
  simp only [thetaWeighted, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- **Unbiased weighted estimators** (Achaz 2009; Ramos-Onsins et al. 2023, Eqs. (5)–(6)): if
each `ξ i` is integrable with the neutral mean `E ξ_i = θ L / i` for `1 ≤ i ≤ n - 1` and
`L ≠ 0`, the estimator `θ̂_w = L⁻¹ ∑_{i=1}^{n-1} i w_i ξ_i` with `∑_{i=1}^{n-1} w_i = 1` has mean
`θ` (`VariableSFS.integral_thetaWeighted` for the rate `θ L` of the whole sequence). -/
theorem integral_thetaWeighted_div (hξ_int : ∀ i, Integrable (ξ i) μ) {θ L : ℝ} (hL : L ≠ 0)
    (hξ : ∀ i ∈ Ico 1 n, μ[ξ i] = θ * L / i) {w : ℕ → ℝ} (hw : ∑ i ∈ Ico 1 n, w i = 1) :
    μ[fun ω => thetaWeighted n w ξ ω / L] = θ := by
  rw [integral_div, integral_thetaWeighted hξ_int hξ hw, mul_div_cancel_right₀ _ hL]

/-- **A test from two estimators** (Ramos-Onsins et al. 2023, Eq. (7)): for a sequence length
`L > 0` and weights `w`, `w'`, the test with weights `W_i = w_i - w'_i` is the standardized
difference `(θ̂_w - θ̂_w') / √Var_μ(θ̂_w - θ̂_w')` of the estimators
`θ̂_w = L⁻¹ ∑_{i=1}^{n-1} i w_i ξ_i` and `θ̂_w'`. When `∑_i w_i = ∑_i w'_i = 1` these are unbiased
estimators of `θ` under the neutral means (`integral_thetaWeighted_div`), and the weights
`w_i - w'_i` sum to `0`. -/
theorem linearNeutralityTest_sub {L : ℝ} (hL : 0 < L) (w w' : ℕ → ℝ) :
    linearNeutralityTest μ n (fun i => w i - w' i) ξ =
      fun ω => (thetaWeighted n w ξ ω / L - thetaWeighted n w' ξ ω / L) /
        √(Var[fun ω => thetaWeighted n w ξ ω / L - thetaWeighted n w' ξ ω / L; μ]) := by
  refine linearNeutralityTest_eq_of_eq_const_mul hL
    (fun ω => thetaWeighted n w ξ ω / L - thetaWeighted n w' ξ ω / L) ?_
  funext ω
  rw [mul_sub, mul_div_cancel₀ _ hL.ne', mul_div_cancel₀ _ hL.ne']
  simp only [thetaWeighted, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-! ### Weight-consistent scaling -/

/-- **Centred weight-consistent weights** (Ramos-Onsins et al. 2023, Eq. (9)): from a weight
function `W` of the frequency `f ∈ (0, 1)`, the weights
`W_i^{(n)} = W(i / n) - (n - 1)⁻¹ ∑_{j=1}^{n-1} W(j / n)`: the values of `W` at the sample
frequencies `i / n`, minus their mean, so that they sum to `0` (`sum_centredWeights`). It is
meaningful for `n ≥ 2`. When `W` has bounded variation on `[0, 1]` and `∫₀¹ W = 0`, the
correction is `O(1 / n)`, so that `W_i^{(n)} ≃ W(i / n)` (`exists_abs_centredWeights_sub_le`). -/
def centredWeights (W : ℝ → ℝ) (n i : ℕ) : ℝ :=
  W ((i : ℝ) / n) - (∑ j ∈ Ico 1 n, W ((j : ℝ) / n)) / ((n : ℝ) - 1)

/-- **Normalized weight-consistent weights** (Ramos-Onsins et al. 2023, Eq. (10)): from the
weight functions `w`, `w'` of two estimators, the weights
`W_i^{(n)} = w(i / n) / ∑_{j=1}^{n-1} w(j / n) - w'(i / n) / ∑_{j=1}^{n-1} w'(j / n)`: the
difference of the weights of two estimators, each normalized to sum to `1`, so that they sum to
`0` (`sum_normalizedWeights`). With Lean's `x / 0 = 0`, a term whose normalizing sum is `0` is
`0`. When `w` and `w'` have bounded variation on `[0, 1]` and `∫₀¹ w = ∫₀¹ w' = 1`,
`n W_i^{(n)}` is within `O(1 / n)` of `w(i / n) - w'(i / n)`, so that
`n W_i^{(n)} ≃ w(i / n) - w'(i / n)` (`exists_abs_mul_normalizedWeights_sub_le`). -/
def normalizedWeights (w w' : ℝ → ℝ) (n i : ℕ) : ℝ :=
  w ((i : ℝ) / n) / ∑ j ∈ Ico 1 n, w ((j : ℝ) / n) -
    w' ((i : ℝ) / n) / ∑ j ∈ Ico 1 n, w' ((j : ℝ) / n)

/-- For `n ≥ 2` the centred weights sum to `0` over `1 ≤ i ≤ n - 1`. -/
theorem sum_centredWeights (W : ℝ → ℝ) (hn : 2 ≤ n) :
    ∑ i ∈ Ico 1 n, centredWeights W n i = 0 := by
  have h : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp only [centredWeights, sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, mul_div_cancel₀ _ h, sub_self]

/-- When both normalizing sums `∑_{j=1}^{n-1} w(j / n)` and `∑_{j=1}^{n-1} w'(j / n)` are
nonzero, the normalized weights sum to `0` over `1 ≤ i ≤ n - 1`. -/
theorem sum_normalizedWeights {w w' : ℝ → ℝ} (hw : ∑ j ∈ Ico 1 n, w ((j : ℝ) / n) ≠ 0)
    (hw' : ∑ j ∈ Ico 1 n, w' ((j : ℝ) / n) ≠ 0) :
    ∑ i ∈ Ico 1 n, normalizedWeights w w' n i = 0 := by
  simp only [normalizedWeights, sum_sub_distrib, ← sum_div, div_self hw, div_self hw', sub_self]

/-- **The normalized weights ignore constant factors** (Ramos-Onsins et al. 2023,
Section 2.2.2): multiplying the weight functions by nonzero constants `c`, `c'` does not change
the normalized weights. A weight function that diverges like `1 / f` or faster at `f = 0` has a
divergent integral, cut off at the inverse population size `1 / N`, so its normalization depends
on `N`; for Watterson's estimator it is `1 / (f log N)`. That dependence is a constant factor,
which drops out of the normalized weights. -/
theorem normalizedWeights_const_mul (w w' : ℝ → ℝ) {c c' : ℝ} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    normalizedWeights (fun f => c * w f) (fun f => c' * w' f) n = normalizedWeights w w' n := by
  funext i
  simp only [normalizedWeights, ← mul_sum, mul_div_mul_left _ _ hc, mul_div_mul_left _ _ hc']

/-- For `n = 3`, the first centred weight of `2 (1 - f) - c / f`, Tajima's weight function
`2 (1 - f)` (of `θ_π`) against Watterson's weight function `1 / f` scaled by `c`, is
`1 / 3 - 3 c / 4`. With the cutoff at the inverse population size `1 / N`, Watterson's weight
function is `1 / (f log N)`, so `c = 1 / log N`. -/
theorem centredWeights_three_one (c : ℝ) :
    centredWeights (fun f => 2 * (1 - f) - c / f) 3 1 = 1 / 3 - 3 * c / 4 := by
  simp only [centredWeights, show (Ico 1 3 : Finset ℕ) = {1, 2} by decide]
  rw [sum_pair (by norm_num)]
  norm_num
  ring

/-- **The centred weights depend on the cutoff** (Ramos-Onsins et al. 2023, Section 2.2.2):
for `n = 3`, the centred weights of `2 (1 - f) - c / f` for `c = 1 / 4` and for `c = 1` are
related by no positive factor, which would leave the test unchanged
(`linearNeutralityTest_const_mul`): their first entries `7 / 48` and `-5 / 12` have opposite
signs (`centredWeights_three_one`). The normalized weights of `2 (1 - f)` and `c / f` do not
depend on `c ≠ 0` (`normalizedWeights_const_mul`), so of the two forms only the normalized one
avoids the dependence on the cutoff `N` in `c = 1 / log N`. -/
theorem not_exists_centredWeights_three_eq_const_mul :
    ¬ ∃ a : ℝ, 0 < a ∧ ∀ i ∈ Ico 1 3,
      centredWeights (fun f => 2 * (1 - f) - 1 / f) 3 i =
        a * centredWeights (fun f => 2 * (1 - f) - (1 / 4) / f) 3 i := by
  rintro ⟨a, ha, h⟩
  have h1 := h 1 (by decide)
  rw [centredWeights_three_one, centredWeights_three_one] at h1
  nlinarith

/-! ### The `O(1 / n)` bounds -/

/-- For `f` monotone on `[0, 1]` and `n ≥ 1`, the Riemann sum `∑_{j=0}^{n-1} f((j + 1) / n)` is
between `n ∫₀¹ f` and `n ∫₀¹ f + f 1 - f 0`. -/
private lemma monotoneOn_sum_bounds {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 0 1)) {n : ℕ}
    (hn : 0 < n) :
    (n : ℝ) * (∫ x in (0 : ℝ)..1, f x) ≤ ∑ j ∈ range n, f (((j : ℝ) + 1) / n) ∧
      ∑ j ∈ range n, f (((j : ℝ) + 1) / n) ≤ (n : ℝ) * (∫ x in (0 : ℝ)..1, f x) + (f 1 - f 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hg : MonotoneOn (fun x => f (x / n)) (Set.Icc 0 (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    rw [zero_add] at hx hy
    refine hf ⟨div_nonneg hx.1 hn'.le, (div_le_one hn').2 hx.2⟩
      ⟨div_nonneg hy.1 hn'.le, (div_le_one hn').2 hy.2⟩ ?_
    exact div_le_div_of_nonneg_right hxy hn'.le
  have hint : ∫ x in (0 : ℝ)..(0 + (n : ℝ)), f (x / n) = n * ∫ x in (0 : ℝ)..1, f x := by
    rw [zero_add, intervalIntegral.integral_comp_div f hn'.ne', zero_div, div_self hn'.ne',
      smul_eq_mul]
  have h1 := hg.integral_le_sum
  have h2 := hg.sum_le_integral
  rw [hint] at h1 h2
  have hs : ∀ j : ℕ, (0 + ((j + 1 : ℕ) : ℝ)) / n = ((j : ℝ) + 1) / n := fun j => by
    push_cast
    ring
  simp only [hs] at h1
  have htel := sum_range_succ (fun j : ℕ => f ((0 + (j : ℝ)) / n)) n
  rw [sum_range_succ'] at htel
  simp only [zero_add, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div,
    div_self hn'.ne'] at htel h2
  constructor <;> linarith

/-- For `n ≥ 1`, `∑_{j=1}^{n-1} g(j / n) = ∑_{j=0}^{n-1} g((j + 1) / n) - g 1`. -/
private lemma sum_Ico_one_eq {g : ℝ → ℝ} {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ Ico 1 n, g ((j : ℝ) / n) = ∑ j ∈ range n, g (((j : ℝ) + 1) / n) - g 1 := by
  have h1 := sum_Ico_succ_top (show 1 ≤ n from hn) (fun j : ℕ => g ((j : ℝ) / n))
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel] at h1
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [div_self hn', Nat.cast_add, Nat.cast_one] at h1
  have h2 : ∑ k ∈ range n, g ((1 + (k : ℝ)) / n) = ∑ j ∈ range n, g (((j : ℝ) + 1) / n) :=
    sum_congr rfl fun j _ => by rw [add_comm]
  linarith

/-- A function of bounded variation on `[0, 1]` is bounded there, and its sums
`∑_{j=1}^{n-1} f(j / n)` stay within a constant of `n ∫₀¹ f`. -/
private lemma exists_bound_of_boundedVariationOn {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 ≤ M ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M) ∧
      ∀ n : ℕ, |∑ j ∈ Ico 1 n, f ((j : ℝ) / n) - n * ∫ x in (0 : ℝ)..1, f x| ≤ K := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hp01 := hp h0 h1 zero_le_one
  have hq01 := hq h0 h1 zero_le_one
  refine ⟨(p 1 - p 0) + (q 1 - q 0) + |p 1 - q 1|, |p 0| + |p 1| + |q 0| + |q 1|,
    by positivity, by positivity, fun x hx => ?_, fun n => ?_⟩
  · have := hp h0 hx hx.1
    have := hp hx h1 hx.2
    have := hq h0 hx hx.1
    have := hq hx h1 hx.2
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self (p 0), neg_abs_le (p 0), le_abs_self (p 1), neg_abs_le (p 1),
        le_abs_self (q 0), neg_abs_le (q 0), le_abs_self (q 1), neg_abs_le (q 1)]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [zero_le, Ico_eq_empty_of_le, CharP.cast_eq_zero, div_zero, Pi.sub_apply,
        sum_sub_distrib, sum_const, card_empty, zero_nsmul, sub_self, zero_mul, abs_zero]
      positivity
    have hI : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
    have hpi : IntervalIntegrable p MeasureTheory.volume 0 1 :=
      MonotoneOn.intervalIntegrable (hI ▸ hp)
    have hqi : IntervalIntegrable q MeasureTheory.volume 0 1 :=
      MonotoneOn.intervalIntegrable (hI ▸ hq)
    obtain ⟨hp1, hp2⟩ := monotoneOn_sum_bounds hp hn
    obtain ⟨hq1, hq2⟩ := monotoneOn_sum_bounds hq hn
    rw [sum_Ico_one_eq hn]
    simp only [Pi.sub_apply, sum_sub_distrib]
    rw [intervalIntegral.integral_sub hpi hqi, abs_le]
    constructor <;> linarith [le_abs_self (p 1 - q 1), neg_abs_le (p 1 - q 1)]

/-- **The centred weights follow the weight function** (Ramos-Onsins et al. 2023, Eqs. (8)–(9)):
for a weight function `W` of bounded variation on `[0, 1]` with `∫₀¹ W = 0`, there is a
constant `C` with `|W_i^{(n)} - W(i / n)| ≤ C / n` for every `n ≥ 2` and every `i`, where
`W_i^{(n)} = centredWeights W n i`. -/
theorem exists_abs_centredWeights_sub_le {W : ℝ → ℝ}
    (hW : BoundedVariationOn W (Set.Icc 0 1)) (hint : ∫ f in (0 : ℝ)..1, W f = 0) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i : ℕ, |centredWeights W n i - W ((i : ℝ) / n)| ≤ C / n := by
  obtain ⟨K, -, hK, -, -, hsum⟩ := exists_bound_of_boundedVariationOn hW
  refine ⟨2 * K, fun n hn i => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := hsum n
  rw [hint, mul_zero, sub_zero] at h
  rw [centredWeights, sub_sub_cancel_left, abs_neg, abs_div,
    abs_of_pos (by linarith : (0 : ℝ) < n - 1), div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [abs_nonneg (∑ j ∈ Ico 1 n, W ((j : ℝ) / n))]

/-- Under the hypotheses of `exists_abs_mul_normalizedWeights_sub_le`, explicit constants. -/
private lemma exists_bound_normalizedWeights {w w' : ℝ → ℝ}
    (hw : BoundedVariationOn w (Set.Icc 0 1)) (hw' : BoundedVariationOn w' (Set.Icc 0 1))
    (hint : ∫ f in (0 : ℝ)..1, w f = 1) (hint' : ∫ f in (0 : ℝ)..1, w' f = 1) :
    ∃ K K' C : ℝ, ∃ N : ℕ, 0 ≤ K ∧ 0 ≤ K' ∧
      (∀ n : ℕ, |∑ j ∈ Ico 1 n, w ((j : ℝ) / n) - n| ≤ K) ∧
      (∀ n : ℕ, |∑ j ∈ Ico 1 n, w' ((j : ℝ) / n) - n| ≤ K') ∧
      ∀ n ≥ N, ∀ i ∈ Ico 1 n,
        |n * normalizedWeights w w' n i - (w ((i : ℝ) / n) - w' ((i : ℝ) / n))| ≤ C / n := by
  obtain ⟨K, M, hK, hM, hbd, hsum⟩ := exists_bound_of_boundedVariationOn hw
  obtain ⟨K', M', hK', hM', hbd', hsum'⟩ := exists_bound_of_boundedVariationOn hw'
  simp only [hint, hint', mul_one] at hsum hsum'
  refine ⟨K, K', 2 * M * K + 2 * M' * K', ⌈2 * (K + K')⌉₊ + 1, hK, hK', hsum, hsum',
    fun n hn i hi => ?_⟩
  have hnN : 2 * (K + K') + 1 ≤ (n : ℝ) := by
    have := Nat.le_ceil (2 * (K + K'))
    have : ((⌈2 * (K + K')⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  set A := ∑ j ∈ Ico 1 n, w ((j : ℝ) / n) with hA
  set A' := ∑ j ∈ Ico 1 n, w' ((j : ℝ) / n) with hA'
  have hAK := abs_le.1 (hsum n)
  have hAK' := abs_le.1 (hsum' n)
  have hApos : (n : ℝ) ≤ 2 * A := by linarith
  have hApos' : (n : ℝ) ≤ 2 * A' := by linarith
  have hA0 : 0 < A := by linarith
  have hA0' : 0 < A' := by linarith
  have hx : (i : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
    have : (i : ℝ) < n := by exact_mod_cast (mem_Ico.1 hi).2
    exact ⟨by positivity, (div_le_one hn0).2 this.le⟩
  have hwx := hbd _ hx
  have hwx' := hbd' _ hx
  have heq : (n : ℝ) * normalizedWeights w w' n i - (w ((i : ℝ) / n) - w' ((i : ℝ) / n)) =
      w ((i : ℝ) / n) * (n - A) / A - w' ((i : ℝ) / n) * (n - A') / A' := by
    rw [normalizedWeights, ← hA, ← hA']
    field_simp
    ring
  have hb : ∀ {v : ℝ} {B KB MB : ℝ}, 0 < B → (n : ℝ) ≤ 2 * B → |B - n| ≤ KB → |v| ≤ MB →
      0 ≤ MB → |v * (n - B) / B| ≤ 2 * MB * KB / n := by
    intro v B KB MB hB hnB hBK hv hMB
    rw [abs_div, abs_mul, abs_of_pos hB, div_le_div_iff₀ hB hn0, abs_sub_comm]
    have h1 : |v| * |B - n| ≤ MB * KB := mul_le_mul hv hBK (abs_nonneg _) hMB
    have h2 : 0 ≤ MB * KB := le_trans (mul_nonneg (abs_nonneg _) (abs_nonneg _)) h1
    nlinarith
  rw [heq, add_div]
  calc _ ≤ |w ((i : ℝ) / n) * (n - A) / A| + |w' ((i : ℝ) / n) * (n - A') / A'| :=
        abs_sub _ _
    _ ≤ _ := add_le_add (hb hA0 hApos (hsum n) hwx hM) (hb hA0' hApos' (hsum' n) hwx' hM')

/-- **The normalized weights follow the weight functions** (Ramos-Onsins et al. 2023,
Eqs. (8) and (10)): for weight functions `w`, `w'` of bounded variation on `[0, 1]` with
`∫₀¹ w = ∫₀¹ w' = 1`, there are `C` and `N` with
`|n W_i^{(n)} - (w(i / n) - w'(i / n))| ≤ C / n` for `n ≥ N` and `1 ≤ i ≤ n - 1`, where
`W_i^{(n)} = normalizedWeights w w' n i`. The normalized weights are of order `1 / n`; the factor
`n` does not change the test (`linearNeutralityTest_const_mul`). -/
theorem exists_abs_mul_normalizedWeights_sub_le {w w' : ℝ → ℝ}
    (hw : BoundedVariationOn w (Set.Icc 0 1)) (hw' : BoundedVariationOn w' (Set.Icc 0 1))
    (hint : ∫ f in (0 : ℝ)..1, w f = 1) (hint' : ∫ f in (0 : ℝ)..1, w' f = 1) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Ico 1 n,
      |n * normalizedWeights w w' n i - (w ((i : ℝ) / n) - w' ((i : ℝ) / n))| ≤ C / n := by
  obtain ⟨-, -, C, N, -, -, -, -, h⟩ := exists_bound_normalizedWeights hw hw' hint hint'
  exact ⟨C, N, h⟩

/-- **The two weight-consistent forms agree to `O(1 / n)`** (Ramos-Onsins et al. 2023,
Section 2.2.1): for weight functions `w`, `w'` of bounded variation on `[0, 1]` with
`∫₀¹ w = ∫₀¹ w' = 1`, the normalized weights of `w`, `w'`, multiplied by `n`, and the centred
weights of `w - w'` differ by at most `C / n` for `n ≥ N` and `1 ≤ i ≤ n - 1`, for some `C` and
`N`. The factor `n` does not change the test (`linearNeutralityTest_const_mul`). -/
theorem exists_abs_mul_normalizedWeights_sub_centredWeights_le {w w' : ℝ → ℝ}
    (hw : BoundedVariationOn w (Set.Icc 0 1)) (hw' : BoundedVariationOn w' (Set.Icc 0 1))
    (hint : ∫ f in (0 : ℝ)..1, w f = 1) (hint' : ∫ f in (0 : ℝ)..1, w' f = 1) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Ico 1 n,
      |n * normalizedWeights w w' n i - centredWeights (fun f => w f - w' f) n i| ≤ C / n := by
  obtain ⟨K, K', C, N, hK, hK', hsum, hsum', h⟩ := exists_bound_normalizedWeights hw hw' hint hint'
  refine ⟨C + 2 * (K + K'), max N 2, fun n hn i hi => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hc : |(w ((i : ℝ) / n) - w' ((i : ℝ) / n)) - centredWeights (fun f => w f - w' f) n i| ≤
      2 * (K + K') / n := by
    rw [centredWeights, sub_sub_cancel, sum_sub_distrib, abs_div,
      abs_of_pos (by linarith : (0 : ℝ) < n - 1), div_le_div_iff₀ (by linarith) (by linarith)]
    have h1 := abs_le.1 (hsum n)
    have h2 := abs_le.1 (hsum' n)
    have h3 : |∑ j ∈ Ico 1 n, w ((j : ℝ) / n) - ∑ j ∈ Ico 1 n, w' ((j : ℝ) / n)| ≤ K + K' := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith [abs_nonneg (∑ j ∈ Ico 1 n, w ((j : ℝ) / n) - ∑ j ∈ Ico 1 n, w' ((j : ℝ) / n))]
  calc _ ≤ |n * normalizedWeights w w' n i - (w ((i : ℝ) / n) - w' ((i : ℝ) / n))| +
        |(w ((i : ℝ) / n) - w' ((i : ℝ) / n)) - centredWeights (fun f => w f - w' f) n i| :=
        abs_sub_le _ _ _
    _ ≤ C / n + 2 * (K + K') / n := add_le_add (h n (le_of_max_le_left hn) i hi) hc
    _ = _ := by rw [add_div]

/-! ### Fay and Wu's `H` -/

/-- `∑_{j=1}^{n-1} j = n (n - 1) / 2`. -/
private lemma sum_Ico_one_cast (n : ℕ) : ∑ j ∈ Ico 1 n, (j : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [sum_Ico_succ_top hn, ih]
    push_cast
    ring

/-- **Fay and Wu's `H`** (Ramos-Onsins et al. 2023, Eq. (11)): for `n ≥ 2`, the normalized
weights of `w(f) = 1` and `w'(f) = 2 f`, and the centred weights of `W(f) = 1 - 2 f`, give the
same test: the standardized `H / √Var_μ(H)` of Fay and Wu's `H = θ_π - θ_H`
(`VariableSFS.fayWuH`). -/
theorem linearNeutralityTest_fayWuH (hn : 2 ≤ n) :
    linearNeutralityTest μ n (normalizedWeights (fun _ => 1) (fun f => 2 * f) n) ξ =
        (fun ω => fayWuH n ξ ω / √(Var[fayWuH n ξ; μ])) ∧
      linearNeutralityTest μ n (centredWeights (fun f => 1 - 2 * f) n) ξ =
        fun ω => fayWuH n ξ ω / √(Var[fayWuH n ξ; μ]) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hcard : ((Ico 1 n).card : ℝ) = n - 1 := by
    rw [Nat.card_Ico, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hs1 : ∑ j ∈ Ico 1 n, (fun _ : ℝ => (1 : ℝ)) ((j : ℝ) / n) = n - 1 := by
    simp only [sum_const, nsmul_eq_mul, mul_one, hcard]
  have hs2 : ∑ j ∈ Ico 1 n, (fun f : ℝ => 2 * f) ((j : ℝ) / n) = n - 1 := by
    simp only [← mul_sum, ← sum_div, sum_Ico_one_cast]
    field_simp
  have hs3 : ∑ j ∈ Ico 1 n, (fun f : ℝ => 1 - 2 * f) ((j : ℝ) / n) = 0 := by
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, hcard, ← mul_sum, ← sum_div,
      sum_Ico_one_cast]
    field_simp
    ring
  have hC : ((n.choose 2 : ℕ) : ℝ) = n * (n - 1) / 2 := Nat.cast_choose_two ℝ n
  have hH : ∀ ω, fayWuH n ξ ω =
      ∑ i ∈ Ico 1 n, ((n : ℝ) - 2 * i) / (n.choose 2 : ℝ) * i * ξ i ω := fun ω => by
    simp only [fayWuH, thetaPi, thetaH, thetaWeighted, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  constructor
  · refine linearNeutralityTest_eq_of_eq_const_mul (c := 1 / 2) (by norm_num) _ ?_
    funext ω
    rw [hH, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [normalizedWeights, hs1, hs2, hC]
    field_simp
  · refine linearNeutralityTest_eq_of_eq_const_mul (c := ((n : ℝ) - 1) / 2) (by linarith) _ ?_
    funext ω
    rw [hH, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [centredWeights, hs3, hC, zero_div, sub_zero]
    field_simp

end MathlibExt.Biology.PopulationGenetics.Coalescent.LinearNeutralityTest

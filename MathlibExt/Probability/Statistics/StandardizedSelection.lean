/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Standardized threshold selection

For a real score `f` on a measure space `(Ω, μ)`, this file defines totalized standardization and
truncation-selection formulas built from Mathlib's integral `μ[f]`, variance `Var[f; μ]`,
covariance `cov[f, g; μ]`, and conditional measure `μ[|s]`. When `μ` is a probability measure and
the scores are square-integrable (with positive variances where divided by standard deviations, and
positive mass `μ s > 0` for a measurable event `s`), these recover the standard statistical
objects of truncation selection in quantitative genetics: population standard deviation, Pearson
correlation, standardized score, standardized upper-tail event, and difference of population means.

## Main definitions

* `populationSD μ f`: `√Var[f; μ]` (population standard deviation when `μ` is a probability measure
  and `f` is square-integrable).
* `pearsonRatio μ f g`: `cov[f, g; μ] / (populationSD μ f * populationSD μ g)` (Pearson correlation
  when `μ` is a probability measure, `f` and `g` are square-integrable, and both variances are
  positive; `0` when either variance is zero).
* `standardizedValue μ f`: `(f - μ[f]) / populationSD μ f` (standardized score when `μ` is a
  probability measure, `f` is square-integrable, and `Var[f; μ] > 0`).
* `standardizedUpperEvent μ f z`: the threshold set `{ω | μ[f] + z * populationSD μ f ≤ f ω}`
  (a measurable upper-tail event when `Measurable f`, with mean and standard deviation
  interpretation when `μ` is a probability measure and `f` is square-integrable).
* `conditionalMeanShift μ H s`: the totalized integral shift `(∫ ω, H ω ∂μ[|s]) - ∫ ω, H ω ∂μ`
  (the difference of population means when `μ` is a probability measure, `H` is integrable, and `s`
  is a measurable event of positive mass).

## Main results

* `conditionalMeanShift_eq_indicator_quotient`: the shift as a quotient of indicator integrals.
* `standardizedUpperEvent_const_mul`, `standardizedUpperEvent_neg`: behavior of the upper event
  under positive rescaling and negation of the score.
* `memLp_dotProduct`, `covariance_dotProduct_left`, `covariance_dotProduct_dotProduct`: second
  moments and covariances of linear combinations `b ⬝ᵥ X` of a random vector.
* `pearsonRatio_eq_zero_of_covariance_eq_zero`,
  `pearsonRatio_linear_eq_zero_of_crossCovariance_eq_zero`: zero covariance gives zero
  `pearsonRatio` quotient.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix

namespace ProbabilityTheory

/-- The square root `√Var[f; μ]` of Mathlib's variance of `f` under `μ`. When `μ` is a
probability measure and `f` is square-integrable, this is the population standard deviation of
`f`. -/
noncomputable def populationSD {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) : ℝ := √Var[f; μ]

/-- The totalized quotient `cov[f, g; μ] / (populationSD μ f * populationSD μ g)` (equal to `0`
by Lean's convention for division by zero when either variance is zero). When `μ` is a
probability measure, `f` and `g` are square-integrable, and both variances are positive, this is
the Pearson correlation of `f` and `g`. -/
noncomputable def pearsonRatio {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) : ℝ := cov[f, g; μ] / (populationSD μ f * populationSD μ g)

/-- The totalized quotient `(f ω - μ[f]) / populationSD μ f`. When `μ` is a probability measure,
`f` is square-integrable, and `Var[f; μ] > 0`, this is the standardized score of `f` in units of
its population standard deviation. -/
noncomputable def standardizedValue {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (ω : Ω) : ℝ := (f ω - μ[f]) / populationSD μ f

/-- The threshold set `{ω | μ[f] + z * populationSD μ f ≤ f ω}` (a measurable upper-tail event
when `Measurable f`; `MemLp` alone gives only a.e. strong measurability). When `μ` is a
probability measure and `f` is square-integrable, the threshold is `z` population standard
deviations above the population mean. -/
noncomputable def standardizedUpperEvent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (z : ℝ) : Set Ω := {ω | μ[f] + z * populationSD μ f ≤ f ω}

/-- The totalized integral shift `(∫ ω, f ω ∂μ[|s]) - ∫ ω, f ω ∂μ`, where `μ[|s]` is the scaled
restriction `(μ s)⁻¹ • μ.restrict s` (normalized to a probability measure when `0 < μ s < ∞`, and
the zero measure when `μ s = 0` or `μ s = ∞`) and the second term is the unnormalized Bochner
integral against `μ`. When `μ` is a probability measure, `f` is integrable, and `s` is a
measurable event of positive mass, this is the difference of population means (the selection
differential of `f` under selection on `s`). -/
noncomputable def conditionalMeanShift {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (s : Set Ω) : ℝ := (∫ ω, f ω ∂μ[|s]) - μ[f]

/-- **The conditional mean shift as an indicator quotient.** Let `μ` be a finite measure on `Ω`,
`s` a measurable event with `μ s > 0`, and `f : Ω → ℝ`. Then
`conditionalMeanShift μ f s = (∫ 1_s f dμ) / (∫ 1_s dμ) - μ[f]`. -/
theorem conditionalMeanShift_eq_indicator_quotient {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} {f : Ω → ℝ}
    (hs : MeasurableSet s) (_hpos : 0 < μ s) :
    conditionalMeanShift μ f s =
      (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω * f ω ∂μ) /
        (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ) - μ[f] := by
  classical
  have hmul : (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * f ω) = s.indicator f := by
    funext ω
    by_cases h : ω ∈ s <;> simp [h]
  rw [conditionalMeanShift, ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul, hmul, integral_indicator hs, integral_indicator hs,
    setIntegral_const, smul_eq_mul, mul_one, div_eq_inv_mul]
  rfl

/-- **Positive rescaling preserves the upper event.** For any measure `μ` on `Ω`, any score
`f : Ω → ℝ`, any threshold `z` and any constant `k > 0`, the standardized upper event of
`ω ↦ k * f ω` at `z` equals the standardized upper event of `f` at `z`. -/
theorem standardizedUpperEvent_const_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Ω → ℝ) (z : ℝ) {k : ℝ} (hk : 0 < k) :
    standardizedUpperEvent μ (fun ω => k * f ω) z = standardizedUpperEvent μ f z := by
  have hSD : populationSD μ (fun ω => k * f ω) = k * populationSD μ f := by
    rw [populationSD, variance_const_mul, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq (le_of_lt hk)]
    rfl
  ext ω
  change (∫ w, k * f w ∂μ) + z * populationSD μ (fun w => k * f w) ≤ k * f ω ↔
    μ[f] + z * populationSD μ f ≤ f ω
  rw [integral_const_mul, hSD]
  rw [show k * μ[f] + z * (k * populationSD μ f) = k * (μ[f] + z * populationSD μ f) by ring]
  exact (mul_le_mul_iff_right₀ hk)

/-- **Negation reflects the upper event.** For any measure `μ` on `Ω`, any score `f : Ω → ℝ` and
any threshold `z`, the standardized upper event of `ω ↦ -f ω` at `z` is the lower event
`{ω | f ω ≤ μ[f] - z * populationSD μ f}` of `f`. -/
theorem standardizedUpperEvent_neg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (z : ℝ) :
    standardizedUpperEvent μ (fun ω => -f ω) z =
      {ω | f ω ≤ μ[f] - z * populationSD μ f} := by
  have hSD : populationSD μ (fun ω => -f ω) = populationSD μ f := by
    rw [populationSD, variance_fun_neg]
    rfl
  ext ω
  change (∫ w, -f w ∂μ) + z * populationSD μ (fun w => -f w) ≤ -f ω ↔
    f ω ≤ μ[f] - z * populationSD μ f
  rw [integral_neg, hSD]
  constructor <;> intro h <;> linarith

/-- **Linear combinations are square integrable.** For any measure `μ` on `Ω` and a random vector
`X : Ω → ℝⁿ` whose coordinates are all in `L²(μ)`, every linear combination `ω ↦ b ⬝ᵥ X ω`,
`b ∈ ℝⁿ`, is in `L²(μ)`. -/
theorem memLp_dotProduct {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → Fin n → ℝ} (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (b : Fin n → ℝ) : MemLp (fun ω => b ⬝ᵥ X ω) 2 μ := by
  convert! memLp_finsetSum' Finset.univ (fun i _ => (hX i).const_mul (b i)) using 1
  funext ω
  simp [dotProduct]

/-- **Covariance of a linear combination with a function.** Let `μ` be a probability measure on
`Ω`, `X : Ω → ℝⁿ` a random vector with all coordinates in `L²(μ)`, `H : Ω → ℝ` in `L²(μ)`, and
`b ∈ ℝⁿ`. Then `cov[b ⬝ᵥ X, H; μ] = b ⬝ᵥ (i ↦ cov[X_i, H; μ])`. -/
theorem covariance_dotProduct_left {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → Fin n → ℝ} {H : Ω → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) (hH : MemLp H 2 μ)
    (b : Fin n → ℝ) :
    cov[fun ω => b ⬝ᵥ X ω, H; μ] =
      b ⬝ᵥ (fun i => cov[fun ω => X ω i, H; μ]) := by
  simp only [dotProduct]
  rw [covariance_fun_sum_left (fun i => (hX i).const_mul (b i)) hH]
  simp only [covariance_const_mul_left]

/-- **Covariance of two linear combinations.** Let `μ` be a probability measure on `Ω`, and
`X, Y : Ω → ℝⁿ` random vectors with all coordinates in `L²(μ)`. For `b, d ∈ ℝⁿ`,
`cov[b ⬝ᵥ X, d ⬝ᵥ Y; μ] = b ⬝ᵥ (C *ᵥ d)`, where `C i j = cov[X_i, Y_j; μ]` is the
cross-covariance matrix. -/
theorem covariance_dotProduct_dotProduct {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → Fin n → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ) (b d : Fin n → ℝ) :
    cov[fun ω => b ⬝ᵥ X ω, fun ω => d ⬝ᵥ Y ω; μ] =
      b ⬝ᵥ ((fun i j => cov[fun ω => X ω i, fun ω => Y ω j; μ]) *ᵥ d) := by
  simp only [dotProduct, mulVec]
  rw [covariance_fun_sum_fun_sum (fun i => (hX i).const_mul (b i))
    (fun j => (hY j).const_mul (d j))]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    Finset.mul_sum]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Zero covariance gives zero Pearson quotient.** Let `μ` be a probability measure on `Ω` and
`f, g : Ω → ℝ` with `Var[f; μ] > 0`, `Var[g; μ] > 0` and `cov[f, g; μ] = 0`. Then the totalized
quotient `pearsonRatio μ f g` equals `0` (this algebraic zero-quotient lemma requires only
`cov[f, g; μ] = 0`, without square-integrability or measurability; when `f, g ∈ L²(μ)`, it
interprets as zero Pearson correlation). -/
theorem pearsonRatio_eq_zero_of_covariance_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (_hf : 0 < Var[f; μ]) (_hg : 0 < Var[g; μ]) (hcov : cov[f, g; μ] = 0) :
    pearsonRatio μ f g = 0 := by
  simp [pearsonRatio, hcov]

/-- **Zero cross-covariance gives zero Pearson quotient for every linear score.** Let `μ` be a
probability measure on `Ω`, `X : Ω → ℝⁿ` with all coordinates in `L²(μ)` and positive definite
covariance matrix `(cov[X_i, X_j; μ])`, and `H : Ω → ℝ` in `L²(μ)` with `Var[H; μ] > 0` and
`cov[X_i, H; μ] = 0` for every `i`. Then for every nonzero `b ∈ ℝⁿ`, the quotient
`pearsonRatio μ (b ⬝ᵥ X) H` equals `0` (and equals the Pearson correlation of `b ⬝ᵥ X` and `H`
since both scores lie in `L²(μ)` with positive variances; the proof itself uses only
`cov[b ⬝ᵥ X, H; μ] = 0`). -/
theorem pearsonRatio_linear_eq_zero_of_crossCovariance_eq_zero
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Fin n → ℝ} {H : Ω → ℝ} (_hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (_hH : MemLp H 2 μ) (_hHpos : 0 < Var[H; μ])
    (_hP : Matrix.PosDef (fun i j => cov[fun ω => X ω i, fun ω => X ω j; μ] :
      Matrix (Fin n) (Fin n) ℝ))
    (_hc : ∀ i, cov[fun ω => X ω i, H; μ] = 0) {b : Fin n → ℝ} (_hb : b ≠ 0) :
    pearsonRatio μ (fun ω => b ⬝ᵥ X ω) H = 0 := by
  have hcov := covariance_dotProduct_left _hX _hH b
  simp only [_hc] at hcov
  simp [pearsonRatio, hcov]

end ProbabilityTheory

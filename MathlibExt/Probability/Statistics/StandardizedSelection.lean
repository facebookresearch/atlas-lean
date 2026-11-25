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

A real score `f` on a measure space `(Ω, μ)` is standardized by its population mean `μ[f]` and
population standard deviation `√Var[f; μ]`. Selecting the individuals whose score is at least
`z` standard deviations above the mean gives the standardized upper event; the change in the mean
of another quantity `H` under the conditional measure of an event is its conditional mean shift.
These are the objects of truncation selection in quantitative genetics.

## Main definitions

* `populationSD μ f`: the population standard deviation `√Var[f; μ]`.
* `pearsonRatio μ f g`: the quotient `cov[f, g; μ] / (populationSD μ f * populationSD μ g)`, the
  correlation of `f` and `g` when both variances are positive.
* `standardizedValue μ f`: the standardized score `(f - μ[f]) / populationSD μ f`.
* `standardizedUpperEvent μ f z`: the event `{ω | μ[f] + z * populationSD μ f ≤ f ω}`.
* `conditionalMeanShift μ H s`: the mean of `H` under `μ[|s]` minus its mean under `μ`.

## Main results

* `conditionalMeanShift_eq_indicator_quotient`: the shift as a quotient of indicator integrals.
* `standardizedUpperEvent_const_mul`, `standardizedUpperEvent_neg`: behavior of the upper event
  under positive rescaling and negation of the score.
* `memLp_dotProduct`, `covariance_dotProduct_left`, `covariance_dotProduct_dotProduct`: second
  moments and covariances of linear combinations `b ⬝ᵥ X` of a random vector.
* `pearsonRatio_eq_zero_of_covariance_eq_zero`,
  `pearsonRatio_linear_eq_zero_of_crossCovariance_eq_zero`: zero covariance gives zero
  correlation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix

namespace ProbabilityTheory

/-- The population standard deviation `√Var[f; μ]` of a real function `f` under the measure `μ`.
-/
noncomputable def populationSD {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) : ℝ := √Var[f; μ]

/-- The Pearson quotient `cov[f, g; μ] / (populationSD μ f * populationSD μ g)`. It is the
correlation of `f` and `g` when both variances are positive (and `0`, by Lean's convention for
division by zero, when either variance is zero). -/
noncomputable def pearsonRatio {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) : ℝ := cov[f, g; μ] / (populationSD μ f * populationSD μ g)

/-- The standardized score `(f ω - μ[f]) / populationSD μ f`, the deviation from the population
mean in units of the population standard deviation (meaningful when `Var[f; μ] > 0`). -/
noncomputable def standardizedValue {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (ω : Ω) : ℝ := (f ω - μ[f]) / populationSD μ f

/-- The standardized upper event `{ω | μ[f] + z * populationSD μ f ≤ f ω}`: the outcomes whose
score is at least `z` population standard deviations above the population mean. -/
noncomputable def standardizedUpperEvent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (z : ℝ) : Set Ω := {ω | μ[f] + z * populationSD μ f ≤ f ω}

/-- The conditional mean shift `∫ f d(μ[|s]) - μ[f]`: the mean of `f` under the conditional
measure of the event `s` minus its mean under `μ`. It is the selection differential of `f` when
`s` has positive measure. -/
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

/-- **Zero covariance gives zero correlation.** Let `μ` be a probability measure on `Ω` and
`f, g : Ω → ℝ` with `Var[f; μ] > 0`, `Var[g; μ] > 0` and `cov[f, g; μ] = 0`. Then
`pearsonRatio μ f g = 0`. -/
theorem pearsonRatio_eq_zero_of_covariance_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (_hf : 0 < Var[f; μ]) (_hg : 0 < Var[g; μ]) (hcov : cov[f, g; μ] = 0) :
    pearsonRatio μ f g = 0 := by
  simp [pearsonRatio, hcov]

/-- **Zero cross-covariance gives zero correlation for every linear score.** Let `μ` be a
probability measure on `Ω`, `X : Ω → ℝⁿ` a random vector with all coordinates in `L²(μ)` and
positive definite covariance matrix `(cov[X_i, X_j; μ])`, and `H : Ω → ℝ` in `L²(μ)` with
`Var[H; μ] > 0` and `cov[X_i, H; μ] = 0` for every `i`. Then for every nonzero `b ∈ ℝⁿ`,
`pearsonRatio μ (b ⬝ᵥ X) H = 0`. -/
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

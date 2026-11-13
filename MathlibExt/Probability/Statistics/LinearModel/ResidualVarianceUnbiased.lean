/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Sampling

/-!
# Unbiasedness of RSS/(n−k) in the Gaussian-free classical linear model

Fixed-design linear model `y = X β + ε` with `X : Matrix m k ℝ` of full column rank
(`IsUnit (Xᵀ * X)`), `p = card k < n = card m`, and errors `ε` that are
square-integrable with `cov[ε i, ε j] = if i = j then σ² else 0` and mean zero.

* The expected quadratic form `E[εᵀ M ε] = σ² * tr M` for any matrix `M`
  (`integral_dotProduct`), from the second-moment identity
  (`second_moment_of_cov`).
* For the residual-maker matrix `M = residualMatrix X`, `tr M = n − p`, so
  `E[RSS/(n−p)] = σ²` (`integral_residualQuadraticForm_div`,
  `integral_rss_div`). No Gaussianity is assumed; only first and second moments.

## Main results

* `integral_dotProduct`, `second_moment_of_cov`.
* `integral_residualQuadraticForm_div`, `integral_rss_div`.

Provenance: the proof bodies were drafted by Muse Code from pinned statements
and were independently checked with Codex before integration.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

/-- **Expected quadratic form**: if `∫ ε_i ε_j = if i = j then σ² else 0`
(with product integrability), then `E[εᵀ M ε] = σ² * tr M` for any matrix `M`.
No symmetry, idempotence, or PSD hypothesis on `M` is needed. -/
theorem integral_dotProduct {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : Type*} [Fintype m] [DecidableEq m] {ε : Ω → m → ℝ}
    (σ : ℝ) (hint : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ)
    (hsecond : ∀ i j, ∫ ω, ε ω i * ε ω j ∂μ = if i = j then σ ^ 2 else 0)
    (M : Matrix m m ℝ) :
    ∫ ω, ε ω ⬝ᵥ M *ᵥ ε ω ∂μ = σ ^ 2 * M.trace := by
  have hMul : ∀ i j, Integrable (fun ω => M i j * (ε ω i * ε ω j)) μ :=
    fun i j => (hint i j).const_mul (M i j)
  have hInner : ∀ i, Integrable (fun ω => ∑ j, M i j * (ε ω i * ε ω j)) μ :=
    fun i => integrable_finsetSum Finset.univ (fun j _ => hMul i j)
  have hEq : ∀ ω, ε ω ⬝ᵥ M *ᵥ ε ω = ∑ i, ∑ j, M i j * (ε ω i * ε ω j) := by
    intro ω
    simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
    congr 1
    ext i
    congr 1
    ext j
    ring
  simp_rw [hEq]
  rw [integral_finsetSum Finset.univ (fun i _ => hInner i)]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hMul _ j)]
  simp_rw [integral_const_mul, hsecond]
  simp_rw [mul_ite, mul_zero]
  simp_rw [Finset.sum_ite_eq _ _ (fun j => M _ j * σ ^ 2)]
  simp only [Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]
  simp only [Matrix.trace, Matrix.diag_apply]
  ring

/-- **Second moments from covariance + mean zero**: if
`cov[ε i, ε j] = if i = j then σ² else 0` and `E[ε i] = 0` for all `i`, then
`∫ ε_i ε_j = if i = j then σ² else 0`. -/
theorem second_moment_of_cov {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : Type*} [Fintype m] [DecidableEq m] {ε : Ω → m → ℝ}
    (σ : ℝ) (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = if i = j then σ ^ 2 else 0)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) (i j : m) :
    ∫ ω, ε ω i * ε ω j ∂μ = if i = j then σ ^ 2 else 0 := by
  have h := hcov i j
  rw [covariance_eq_sub (hL2 i) (hL2 j)] at h
  rw [hmean i, hmean j] at h
  simp only [mul_zero, sub_zero] at h
  exact h

/-- **Expected residual quadratic form**: `E[εᵀ M ε / (n − k)] = σ²` for the
residual-maker matrix `M`, since `tr M = n − k`. -/
theorem integral_residualQuadraticForm_div {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X))
    (hkm : Fintype.card k < Fintype.card m) {ε : Ω → m → ℝ} (σ : ℝ)
    (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = if i = j then σ ^ 2 else 0)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
    ∫ ω, (ε ω ⬝ᵥ residualMatrix X *ᵥ ε ω) /
      ((Fintype.card m : ℝ) - (Fintype.card k : ℝ)) ∂μ = σ ^ 2 := by
  have hint : ∀ i j, Integrable (fun ω => ε ω i * ε ω j) μ :=
    fun i j => (hL2 i).integrable_mul (hL2 j)
  have hsecond : ∀ i j, ∫ ω, ε ω i * ε ω j ∂μ = if i = j then σ ^ 2 else 0 :=
    fun i j => second_moment_of_cov σ hL2 hcov hmean i j
  have hQ := integral_dotProduct σ hint hsecond (residualMatrix X)
  rw [trace_residualMatrix hX] at hQ
  have hne : ((Fintype.card m : ℝ) - (Fintype.card k : ℝ)) ≠ 0 := by
    have h : (Fintype.card k : ℝ) < (Fintype.card m : ℝ) := Nat.cast_lt.mpr hkm
    exact sub_ne_zero.mpr (ne_of_gt h)
  rw [integral_div, hQ]
  exact mul_div_cancel_right₀ (σ ^ 2) hne

/-- **RSS/(n−k) is unbiased for σ²**: the residual sum of squares divided by `n − k`
has expectation `σ²` under the frozen model. No Gaussianity is assumed. -/
theorem integral_rss_div {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X))
    (hkm : Fintype.card k < Fintype.card m) (β : k → ℝ) {ε : Ω → m → ℝ} (σ : ℝ)
    (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = if i = j then σ ^ 2 else 0)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
    ∫ ω, ((X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
        (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω))) /
        ((Fintype.card m : ℝ) - (Fintype.card k : ℝ)) ∂μ = σ ^ 2 := by
  simp_rw [rss_eq_dotProduct_residualMatrix hX β]
  exact integral_residualQuadraticForm_div hX hkm σ hL2 hcov hmean

end MathlibExt.Probability.Statistics.LinearModel

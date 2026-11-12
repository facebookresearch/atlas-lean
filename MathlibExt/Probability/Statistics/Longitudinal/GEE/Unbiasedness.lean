/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Generalized estimating equations: unbiasedness at the target parameter

Clusters `i : ι` (a finite type, `n = card ι`) carry a response vector `Yᵢ : Tᵢ → ℝ` over a
finite, cluster-specific index type `Tᵢ` (unbalanced cluster sizes are allowed). The regression
parameter is `β : κ → ℝ`. Cluster `i` has

* a **marginal mean model** `μᵢ(β) : Tᵢ → ℝ` (`mean i β`), in which the covariates `Xᵢ` enter;
* its Jacobian `Dᵢ(β) = ∂μᵢ/∂β : Matrix Tᵢ κ ℝ` (`meanJacobian`), defined through `fderiv`;
* a **declared working covariance** `Vᵢ(β) : Matrix Tᵢ Tᵢ ℝ` (`V i β`), an arbitrary chosen
  matrix that may depend on `β` and that need not equal `Cov(Yᵢ)`. `Vᵢ⁻¹` is Mathlib's
  nonsingular inverse (`0` for a singular matrix), so for singular `Vᵢ` the cluster contributes
  nothing, and the results are only meaningful for invertible `Vᵢ`.

The GEE estimating function of Liang and Zeger (1986) is (`geeEstFun`)

`U(β) = ∑ᵢ Dᵢ(β)ᵀ Vᵢ(β)⁻¹ (Yᵢ - μᵢ(β))`.

## Main results

* `integral_sum_mulVec_sub_eq_zero`: for any fixed matrices `Aᵢ`, if `E[Yᵢ] = mᵢ` then
  `E[∑ᵢ Aᵢ (Yᵢ - mᵢ)] = 0`.
* `integral_geeEstFun_eq_zero`: **unbiasedness, fixed design.** If every `Yᵢ` is integrable and
  the mean model is correct at `β*` (`E[Yᵢ] = μᵢ(β*)`), then `E[U(β*)] = 0`.
* `integral_mulVec_eq_zero_of_condExp_eq_zero`: if a random weight matrix `W` is measurable for a
  sub-σ-algebra `m` and `E[R | m] = 0`, then `E[W R] = 0`.
* `integral_geeEstFun_covariates_eq_zero`: **unbiasedness, random covariates.** With random
  cluster covariates `Xᵢ`, a mean model `μᵢ(x, β)` and a working covariance `Vᵢ(x, β)`, if the
  conditional mean is correct, `E[Yᵢ | Xᵢ] = μᵢ(Xᵢ, β*)`, then `E[U(β*)] = 0`.
* `meanJacobian_mulVec`: for a linear mean `μ(β) = X β`, `D = X`.

## What the proofs use

The working covariances `V` are universally quantified and appear in no hypothesis, so the
theorems hold for every declared `Vᵢ`, correct or not, provided `Vᵢ` is deterministic (or, in the
random-covariate theorem, a function of `(Xᵢ, β)` only). A working correlation `α̂` or scale `φ̂`
estimated from the responses of all clusters makes the weights depend on `Y`, so the theorems do
not apply and `E[U(β*; α̂)] = 0` can fail in finite samples; Liang and Zeger recover it only
asymptotically, and that plug-in case is deferred to T35/T36. The fixed-design theorem uses only
`E[Yᵢ] = μᵢ(β*)` and linearity of the integral. Neither theorem assumes independence between
clusters: unbiasedness of `U(β*)` does not need it. Independence is what the variance of `U(β*)`
(the sandwich) and the asymptotics of the root need; those are not treated here.

In the random-covariate theorem `Xᵢ` is the covariate data of the whole cluster, so the hypothesis
is `E[Yᵢₜ | Xᵢ₁, …, Xᵢₘ] = μᵢₜ(Xᵢ, β*)` for every `t`. With time-varying covariates this is
stronger than `E[Yᵢₜ | Xᵢₜ] = μᵢₜ(Xᵢₜ, β*)`, and with a non-diagonal `Vᵢ` the weaker assumption
need not give unbiasedness (Pepe and Anderson, 1994). It does suffice when `Vᵢ` is diagonal and
weight column `t` depends only on `Xᵢₜ`. If the weights of cluster `i` also used other
clusters' covariates, the needed hypothesis would be `E[Yᵢ | X₁, …, Xₙ] = μᵢ(Xᵢ, β*)`;
independent clusters supply it. `integral_mulVec_eq_zero_of_condExp_eq_zero` covers that case
with `m = σ(X₁, …, Xₙ)`.

Unbiasedness is a statement about `U(β*)`, not about its root. With one cluster (`n = 1`) it still
holds exactly, but `∑ᵢ DᵢᵀVᵢ⁻¹Dᵢ` can be singular, so `β*` need not be the only zero of
`β ↦ E[U(β)]` (see the tests), and with nonlinear `μ` the root is in general a biased estimator.

## Reuse search and sources

Searched (2026-11-11, base `53666a3c1`) pinned Mathlib `v4.35.0` and this repository for
estimating equations, GEE, quasi-score, and longitudinal data: no estimating-function API exists.
Reused: Mathlib's `condExp_mul_of_stronglyMeasurable_left` (pull-out),
`integral_condExp` (tower), `eval_integral` and `integrable_pi_iff` (vector-valued integrals),
`ContinuousLinearMap.integral_comp_comm`, and `LinearMap.toMatrix'` for the Jacobian.
`MathlibExt.Probability.Statistics.GeneralizedLeastSquares` (`glsMatrix`) is the linear,
known-covariance special case; it is about estimators rather than estimating functions and is not
imported.

## References

* K.-Y. Liang and S. L. Zeger, *Longitudinal data analysis using generalized linear models*,
  Biometrika 73 (1986), 13–22: the estimating equation `∑ᵢ Dᵢᵀ Vᵢ⁻¹ Sᵢ = 0` with
  `Sᵢ = Yᵢ - μᵢ(β)` and a working correlation, and consistency under a correct mean only.
* M. S. Pepe and G. L. Anderson, *A cautionary note on inference for marginal regression models
  with longitudinal data and general correlated response data*, Comm. Statist. Simulation Comput.
  23 (1994), 939–951.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.Longitudinal.GEE

open Matrix MeasureTheory

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### The estimating function -/

/-- The Jacobian `D(β) = ∂μ/∂β` of a mean model `μ : (κ → ℝ) → τ → ℝ`, as a matrix: entry
`(t, k)` is `∂μₜ/∂βₖ`. It is `0` where `μ` is not differentiable. -/
noncomputable def meanJacobian {τ : Type*} [Fintype τ] (μ : (κ → ℝ) → τ → ℝ) (β : κ → ℝ) :
    Matrix τ κ ℝ :=
  LinearMap.toMatrix' (fderiv ℝ μ β : (κ → ℝ) →ₗ[ℝ] τ → ℝ)

/-- The GEE weight `D(β)ᵀ V⁻¹` of one cluster with mean model `μ` and declared working
covariance `V`. -/
noncomputable def geeWeight {τ : Type*} [Fintype τ] [DecidableEq τ] (μ : (κ → ℝ) → τ → ℝ)
    (V : Matrix τ τ ℝ) (β : κ → ℝ) : Matrix κ τ ℝ :=
  (meanJacobian μ β)ᵀ * V⁻¹

variable {ι : Type*} [Fintype ι] {T : ι → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

/-- The GEE estimating function `U(β) = ∑ᵢ Dᵢ(β)ᵀ Vᵢ(β)⁻¹ (yᵢ - μᵢ(β))` for mean models
`mean i`, declared working covariances `V i` and responses `y i`. -/
noncomputable def geeEstFun (mean : ∀ i, (κ → ℝ) → T i → ℝ)
    (V : ∀ i, (κ → ℝ) → Matrix (T i) (T i) ℝ) (y : ∀ i, T i → ℝ) (β : κ → ℝ) : κ → ℝ :=
  ∑ i, geeWeight (mean i) (V i β) β *ᵥ (y i - mean i β)

/-- For a linear mean model `μ(β) = X β` the Jacobian is the design matrix `X`. -/
theorem meanJacobian_mulVec {τ : Type*} [Fintype τ] (X : Matrix τ κ ℝ) (β : κ → ℝ) :
    meanJacobian (fun b => X *ᵥ b) β = X := by
  have h : fderiv ℝ (fun b => X *ᵥ b) β = LinearMap.toContinuousLinearMap (Matrix.toLin' X) :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' X)).fderiv
  rw [meanJacobian, h]
  exact LinearMap.toMatrix'_toLin' X

/-! ### Unbiasedness with fixed weights -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

omit [DecidableEq κ] [∀ i, DecidableEq (T i)] in
/-- If `E[Yᵢ] = mᵢ` for every cluster, then `E[∑ᵢ Aᵢ (Yᵢ - mᵢ)] = 0` for any fixed matrices
`Aᵢ`. -/
theorem integral_sum_mulVec_sub_eq_zero [IsProbabilityMeasure P]
    (A : ∀ i, Matrix κ (T i) ℝ) (Y : ∀ i, Ω → T i → ℝ) (m : ∀ i, T i → ℝ)
    (hY : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = m i) :
    ∫ ω, ∑ i, A i *ᵥ (Y i ω - m i) ∂P = 0 := by
  have hint : ∀ i, Integrable (fun ω => Y i ω - m i) P := fun i =>
    (hY i).sub (integrable_const _)
  have hterm : ∀ i, Integrable (fun ω => A i *ᵥ (Y i ω - m i)) P := fun i =>
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (A i))).integrable_comp (hint i)
  rw [integral_finsetSum _ fun i _ => hterm i]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (A i))).integral_comp_comm (hint i)
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply] at h
  rw [h, integral_sub (hY i) (integrable_const _), hmean i, integral_const, probReal_univ,
    one_smul, sub_self, mulVec_zero]

/-- **Unbiasedness of the GEE estimating function (fixed design).** If each response `Yᵢ` is
integrable and the marginal mean model is correct at `β*`, `E[Yᵢ] = μᵢ(β*)`, then
`E[U(β*)] = 0`, for every choice of declared working covariances `V`. No independence between
clusters is assumed. -/
theorem integral_geeEstFun_eq_zero [IsProbabilityMeasure P] (mean : ∀ i, (κ → ℝ) → T i → ℝ)
    (V : ∀ i, (κ → ℝ) → Matrix (T i) (T i) ℝ) (Y : ∀ i, Ω → T i → ℝ) (βstar : κ → ℝ)
    (hY : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = mean i βstar) :
    ∫ ω, geeEstFun mean V (fun i => Y i ω) βstar ∂P = 0 :=
  integral_sum_mulVec_sub_eq_zero (fun i => geeWeight (mean i) (V i βstar) βstar) Y
    (fun i => mean i βstar) hY hmean

/-! ### Unbiasedness with random weights -/

omit [DecidableEq κ] in
/-- **Pull-out form.** If the entries of a random weight matrix `W` are measurable for a
sub-σ-algebra `m` and the residual `R` has `E[R | m] = 0`, then `E[W R] = 0`. -/
theorem integral_mulVec_eq_zero_of_condExp_eq_zero {τ : Type*} [Fintype τ] [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {W : Ω → Matrix κ τ ℝ}
    (hW : ∀ k t, StronglyMeasurable[m] fun ω => W ω k t) {R : Ω → τ → ℝ}
    (hR : ∀ t, Integrable (fun ω => R ω t) P)
    (hWR : ∀ k t, Integrable (fun ω => W ω k t * R ω t) P)
    (hcond : ∀ t, P[fun ω => R ω t | m] =ᵐ[P] 0) :
    ∫ ω, W ω *ᵥ R ω ∂P = 0 := by
  have hcomp : ∀ k, Integrable (fun ω => (W ω *ᵥ R ω) k) P := fun k => by
    simpa [mulVec, dotProduct] using integrable_finsetSum _ fun t _ => hWR k t
  ext k
  rw [eval_integral hcomp]
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [integral_finsetSum _ fun t _ => hWR k t]
  refine Finset.sum_eq_zero fun t _ => ?_
  have h : P[fun ω => W ω k t * R ω t | m] =ᵐ[P] fun ω => W ω k t * P[fun ω => R ω t | m] ω :=
    condExp_mul_of_stronglyMeasurable_left (hW k t) (hWR k t) (hR t)
  have h0 : (fun ω => W ω k t * P[fun ω => R ω t | m] ω) =ᵐ[P] 0 := by
    filter_upwards [hcond t] with ω hω
    simp [hω]
  rw [← integral_condExp hm, integral_congr_ae (h.trans h0)]
  simp

/-- **Unbiasedness of the GEE estimating function (random covariates).** Cluster `i` has random
covariates `Xᵢ` with values in `𝒳ᵢ`, a mean model `μᵢ(x, β)` and a declared working covariance
`Vᵢ(x, β)`. If the conditional mean model is correct at `β*`,
`E[Yᵢ | Xᵢ] = μᵢ(Xᵢ, β*)`, the model maps are measurable in `x`, and the moments exist, then
`E[U(β*)] = 0`, for every choice of `V`. No independence between clusters is assumed. -/
theorem integral_geeEstFun_covariates_eq_zero [IsProbabilityMeasure P] {𝒳 : ι → Type*}
    [m𝒳 : ∀ i, MeasurableSpace (𝒳 i)] (X : ∀ i, Ω → 𝒳 i) (hX : ∀ i, Measurable (X i))
    (mean : ∀ i, 𝒳 i → (κ → ℝ) → T i → ℝ) (V : ∀ i, 𝒳 i → (κ → ℝ) → Matrix (T i) (T i) ℝ)
    (Y : ∀ i, Ω → T i → ℝ) (βstar : κ → ℝ)
    (hWmeas : ∀ i k t, Measurable fun x => geeWeight (mean i x) (V i x βstar) βstar k t)
    (hmeanMeas : ∀ i t, Measurable fun x => mean i x βstar t)
    (hY : ∀ i t, Integrable (fun ω => Y i ω t) P)
    (hmeanInt : ∀ i t, Integrable (fun ω => mean i (X i ω) βstar t) P)
    (hWY : ∀ i k t, Integrable (fun ω => geeWeight (mean i (X i ω)) (V i (X i ω) βstar) βstar k t *
      (Y i ω t - mean i (X i ω) βstar t)) P)
    (hcond : ∀ i t, P[fun ω => Y i ω t | (m𝒳 i).comap (X i)] =ᵐ[P]
      fun ω => mean i (X i ω) βstar t) :
    ∫ ω, geeEstFun (fun i => mean i (X i ω)) (fun i => V i (X i ω)) (fun i => Y i ω) βstar ∂P =
      0 := by
  have hterm : ∀ i, Integrable (fun ω => geeWeight (mean i (X i ω)) (V i (X i ω) βstar) βstar *ᵥ
      (Y i ω - mean i (X i ω) βstar)) P := fun i => by
    refine integrable_pi_iff.mpr fun k => ?_
    simpa [mulVec, dotProduct] using integrable_finsetSum _ fun t _ => hWY i k t
  unfold geeEstFun
  rw [integral_finsetSum _ fun i _ => hterm i]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hm : (m𝒳 i).comap (X i) ≤ mΩ := (hX i).comap_le
  refine integral_mulVec_eq_zero_of_condExp_eq_zero hm
    (fun k t => ((hWmeas i k t).comp (comap_measurable (X i))).stronglyMeasurable)
    (fun t => (hY i t).sub (hmeanInt i t)) (hWY i) fun t => ?_
  have hmeanSM : StronglyMeasurable[(m𝒳 i).comap (X i)] fun ω => mean i (X i ω) βstar t :=
    ((hmeanMeas i t).comp (comap_measurable (X i))).stronglyMeasurable
  have hsub := condExp_sub (m := (m𝒳 i).comap (X i)) (hY i t) (hmeanInt i t)
  rw [condExp_of_stronglyMeasurable hm hmeanSM (hmeanInt i t)] at hsub
  refine (hsub.trans ?_)
  filter_upwards [hcond i t] with ω hω
  simp [hω]

end MathlibExt.Probability.Statistics.Longitudinal.GEE

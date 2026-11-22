/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Sampling
public import MathlibExt.Probability.Distributions.CochranIndependence

/-!
# Independence of fitted values and residuals in the Gaussian linear model

Fixed-design linear model `y = X β + ε` with `X : Matrix m k ℝ` of full column rank
(`IsUnit (Xᵀ * X)`) and errors `ε` whose standardized form `σ⁻¹ ε` (`σ > 0`) has
i.i.d. standard normal coordinates. Write `B = (Xᵀ X)⁻¹ Xᵀ` (`olsMatrix`),
`H = X B` (`hatMatrix`) and `M = 1 - X B` (`residualMatrix`).

* `H` is idempotent (`hatMatrix_mul_self`) and annihilates `M`
  (`hatMatrix_mul_residualMatrix`), so the fitted values `H *ᵥ y` and the
  residuals `M *ᵥ y` are orthogonal images.
* The fitted vector is independent of the residual vector
  (`indepFun_fitted_residual`), by the Cochran kernel
  `ProbabilityTheory.indepFun_mulVec_mulVec_of_hasLaw` applied to the pair
  `(H, M)` and an affine transport. The sibling result
  `indepFun_olsEstimator_residual` (in `LinearModel.Inference`) is the
  estimator-vs-residual version; the fitted version here also follows from it
  by `IndepFun.comp` with `X *ᵥ ·`.

## Main results

* `hatMatrix`, `hatMatrix_mul_self`, `hatMatrix_mul_residualMatrix`.
* `fitted_eq_hatMatrix_mulVec`: fitted values are `hatMatrix X *ᵥ y`.
* `indepFun_hatMatrix_mulVec_residualMatrix_mulVec`,
  `indepFun_fitted_residual`.

Provenance: the proof bodies were drafted by Muse Code from pinned statements
and were independently checked with Codex before integration.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

/-! ### ST04.T01: independence of fitted values and residuals -/

namespace MathlibExt.Probability.Statistics.LinearModel

/-- The hat matrix `X * olsMatrix X`: fitted values are `hatMatrix X *ᵥ y`. -/
noncomputable def hatMatrix {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (X : Matrix m k ℝ) : Matrix m m ℝ :=
  X * olsMatrix X

/-- The hat matrix is idempotent: `H * H = H`. -/
theorem hatMatrix_mul_self {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) :
    hatMatrix X * hatMatrix X = hatMatrix X := by
  unfold hatMatrix
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (olsMatrix X) X (olsMatrix X),
    olsMatrix_mul_self hX, Matrix.one_mul]

/-- The hat matrix annihilates the residual-maker matrix: `H * M = 0`. -/
theorem hatMatrix_mul_residualMatrix {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) :
    hatMatrix X * residualMatrix X = 0 := by
  unfold hatMatrix residualMatrix
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc,
    ← Matrix.mul_assoc (olsMatrix X) X (olsMatrix X), olsMatrix_mul_self hX,
    Matrix.one_mul, sub_self]

/-- Fitted values are the hat matrix applied to the response. -/
theorem fitted_eq_hatMatrix_mulVec {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (X : Matrix m k ℝ) (y : m → ℝ) :
    X *ᵥ olsEstimator X y = hatMatrix X *ᵥ y := by
  unfold hatMatrix olsEstimator
  rw [mulVec_mulVec]

/-- **Fitted and residual images are independent** for a standard Gaussian vector:
`IndepFun (H *ᵥ Z) (M *ᵥ Z)` for the hat matrix `H` and residual-maker `M`. -/
theorem indepFun_hatMatrix_mulVec_residualMatrix_mulVec {m k : Type*} [Fintype m]
    [DecidableEq m] [Fintype k] [DecidableEq k] {X : Matrix m k ℝ}
    (hX : IsUnit (Xᵀ * X)) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : Ω → m → ℝ} (hZ : HasLaw Z (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    IndepFun (fun ω => hatMatrix X *ᵥ Z ω) (fun ω => residualMatrix X *ᵥ Z ω) μ := by
  apply ProbabilityTheory.indepFun_mulVec_mulVec_of_hasLaw hZ
  rw [residualMatrix_transpose, hatMatrix_mul_residualMatrix hX]

/-- **Fitted values and residuals are independent** under a spherical Gaussian error law:
in `y = X β + ε` with `σ > 0` and `σ⁻¹ • ε` standard Gaussian, the fitted vector
`X *ᵥ β̂` is independent of the residual vector `y - X *ᵥ β̂`. -/
theorem indepFun_fitted_residual {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) (β : k → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ε : Ω → m → ℝ} {σ : ℝ}
    (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    IndepFun (fun ω => X *ᵥ olsEstimator X (X *ᵥ β + ε ω))
      (fun ω => (X *ᵥ β + ε ω) - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) μ := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hindep : IndepFun (fun ω => hatMatrix X *ᵥ (σ⁻¹ • ε ω))
      (fun ω => residualMatrix X *ᵥ (σ⁻¹ • ε ω)) μ :=
    indepFun_hatMatrix_mulVec_residualMatrix_mulVec hX hε
  have hε_eq : ∀ ω, ε ω = σ • (σ⁻¹ • ε ω) := fun ω => by
    rw [smul_smul, mul_inv_cancel₀ hσne, one_smul]
  have hbeta : ∀ ω, olsEstimator X (X *ᵥ β + ε ω) = β + olsMatrix X *ᵥ ε ω :=
    fun ω => olsEstimator_add hX β (ε ω)
  have hfitted : ∀ ω, X *ᵥ olsEstimator X (X *ᵥ β + ε ω)
      = X *ᵥ β + σ • (hatMatrix X *ᵥ (σ⁻¹ • ε ω)) := fun ω => by
    calc X *ᵥ olsEstimator X (X *ᵥ β + ε ω)
        = X *ᵥ (β + olsMatrix X *ᵥ ε ω) := by rw [hbeta ω]
      _ = X *ᵥ β + X *ᵥ (olsMatrix X *ᵥ ε ω) := by rw [mulVec_add]
      _ = X *ᵥ β + (X * olsMatrix X) *ᵥ ε ω := by rw [mulVec_mulVec]
      _ = X *ᵥ β + hatMatrix X *ᵥ ε ω := rfl
      _ = X *ᵥ β + σ • (hatMatrix X *ᵥ (σ⁻¹ • ε ω)) := by
          nth_rewrite 1 [hε_eq ω]
          rw [mulVec_smul]
  have hresid : ∀ ω, (X *ᵥ β + ε ω) - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)
      = σ • (residualMatrix X *ᵥ (σ⁻¹ • ε ω)) := fun ω => by
    calc (X *ᵥ β + ε ω) - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)
        = residualMatrix X *ᵥ (X *ᵥ β + ε ω) := sub_mulVec_olsEstimator X _
      _ = residualMatrix X *ᵥ ε ω := residualMatrix_mulVec_add hX β (ε ω)
      _ = σ • (residualMatrix X *ᵥ (σ⁻¹ • ε ω)) := by
          nth_rewrite 1 [hε_eq ω]
          rw [mulVec_smul]
  have hφ : Measurable (fun v : m → ℝ => X *ᵥ β + σ • v) := by fun_prop
  have hψ : Measurable (fun v : m → ℝ => σ • v) := by fun_prop
  have hcomp := hindep.comp hφ hψ
  have ef : (fun ω => X *ᵥ olsEstimator X (X *ᵥ β + ε ω))
      = (fun v : m → ℝ => X *ᵥ β + σ • v) ∘
        (fun ω => hatMatrix X *ᵥ (σ⁻¹ • ε ω)) := by
    funext ω
    simp only [Function.comp_apply]
    exact hfitted ω
  have er : (fun ω => (X *ᵥ β + ε ω) - X *ᵥ olsEstimator X (X *ᵥ β + ε ω))
      = (fun v : m → ℝ => σ • v) ∘
        (fun ω => residualMatrix X *ᵥ (σ⁻¹ • ε ω)) := by
    funext ω
    simp only [Function.comp_apply]
    exact hresid ω
  rw [ef, er]
  exact hcomp

end MathlibExt.Probability.Statistics.LinearModel

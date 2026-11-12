/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Inference

/-!
# Linear hypotheses in the Gaussian linear model: the chi-square numerator

Fixed-design linear model `y = X β + ε` with `X : Matrix m k ℝ` of full column rank
(`IsUnit (Xᵀ X)`), `σ > 0` and `σ⁻¹ ε` with i.i.d. standard normal coordinates. Write
`G = (Xᵀ X)⁻¹`, `B = G Xᵀ` (`olsMatrix`), `β̂ = B y` and `M = 1 - X B` (`residualMatrix`). A linear
hypothesis is `C β = c` for `C : Matrix r k ℝ` of full row rank (`IsUnit (C G Cᵀ)`), with
`q = card r` restrictions.

* The hypothesis matrix `H = Bᵀ Cᵀ (C G Cᵀ)⁻¹ C B` is symmetric for every `X` and `C`, and is
  idempotent of rank `q` with `H M = 0` under the rank hypotheses.
* Under `H₀ : C β = c` and `q > 0`, the numerator `(C β̂ - c)ᵀ (C G Cᵀ)⁻¹ (C β̂ - c) / σ²` is
  `χ²_q`: it equals the quadratic form `Zᵀ H Z` of the standardized errors `Z = σ⁻¹ ε`.
* The numerator is independent of `‖y - X β̂‖² / σ²` for every `C` and `c`.

Not covered: the `F` statistic and its `F(q, n - p)` law, confidence ellipsoids, noncentral laws
under alternatives, and test inversion.

## Main results

* `hypothesisMatrix`, `hypothesisMatrix_transpose`, `hypothesisMatrix_isHermitian`,
  `hypothesisMatrix_mul_self`, `rank_hypothesisMatrix`, `hypothesisMatrix_mul_residualMatrix`.
* `hasLaw_linearHypothesis_numerator`: the central `χ²_q` law under `H₀`.
* `indepFun_linearHypothesis_numerator_rss_div_sq`: independence from `RSS / σ²`.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

/-- `((Xᵀ X)⁻¹)ᵀ = (Xᵀ X)⁻¹`. -/
private theorem transpose_gram_inv {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    (X : Matrix m k ℝ) : ((Xᵀ * X)⁻¹)ᵀ = (Xᵀ * X)⁻¹ := by
  rw [transpose_nonsing_inv, transpose_mul, transpose_transpose]

private theorem smul_inv_smul_eq {m : Type*} {σ : ℝ} (hσ : 0 < σ) (e : m → ℝ) :
    σ • σ⁻¹ • e = e := by
  rw [smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]

/-- The hypothesis matrix `H = Bᵀ Cᵀ (C (Xᵀ X)⁻¹ Cᵀ)⁻¹ C B` of the linear hypothesis `C β = c`,
where `B = (Xᵀ X)⁻¹ Xᵀ` is the OLS matrix. Under `C β = c` the numerator of the `F` statistic is
the quadratic form `εᵀ H ε`. -/
noncomputable def hypothesisMatrix {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    (X : Matrix m k ℝ) (C : Matrix r k ℝ) : Matrix m m ℝ :=
  (olsMatrix X)ᵀ * Cᵀ * (C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ * C * olsMatrix X

/-- The hypothesis matrix is symmetric, for every design and hypothesis matrix. -/
theorem hypothesisMatrix_transpose {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    (X : Matrix m k ℝ) (C : Matrix r k ℝ) : (hypothesisMatrix X C)ᵀ = hypothesisMatrix X C := by
  have hW : ((C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹)ᵀ = (C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_mul, transpose_mul, transpose_transpose,
      transpose_gram_inv, Matrix.mul_assoc]
  rw [hypothesisMatrix, transpose_mul, transpose_mul, transpose_mul, transpose_mul,
    transpose_transpose, transpose_transpose, hW]
  simp only [Matrix.mul_assoc]

theorem hypothesisMatrix_isHermitian {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    (X : Matrix m k ℝ) (C : Matrix r k ℝ) : (hypothesisMatrix X C).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hypothesisMatrix_transpose]

/-- The hypothesis matrix is idempotent for a full-rank design and a full-row-rank hypothesis. -/
theorem hypothesisMatrix_mul_self {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    {X : Matrix m k ℝ} {C : Matrix r k ℝ} (hX : IsUnit (Xᵀ * X))
    (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) :
    hypothesisMatrix X C * hypothesisMatrix X C = hypothesisMatrix X C := by
  rw [hypothesisMatrix, show (olsMatrix X)ᵀ * Cᵀ * (C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ * C * olsMatrix X *
      ((olsMatrix X)ᵀ * Cᵀ * (C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ * C * olsMatrix X) =
      (olsMatrix X)ᵀ * Cᵀ * ((C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ * (C * (olsMatrix X * (olsMatrix X)ᵀ) * Cᵀ)) *
        (C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ * C * olsMatrix X by
    simp only [Matrix.mul_assoc]]
  rw [olsMatrix_mul_transpose hX,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hC), Matrix.mul_one]

/-- The hypothesis matrix has rank `q = card r`. -/
theorem rank_hypothesisMatrix {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    {X : Matrix m k ℝ} {C : Matrix r k ℝ} (hX : IsUnit (Xᵀ * X))
    (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) :
    (hypothesisMatrix X C).rank = Fintype.card r := by
  have htr : (hypothesisMatrix X C).trace = (Fintype.card r : ℝ) := by
    rw [hypothesisMatrix, show (olsMatrix X)ᵀ * Cᵀ * (C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ * C * olsMatrix X =
        (olsMatrix X)ᵀ * Cᵀ * ((C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ * C * olsMatrix X) by
      simp only [Matrix.mul_assoc], trace_mul_comm,
      show (C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ * C * olsMatrix X * ((olsMatrix X)ᵀ * Cᵀ) =
        (C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ * (C * (olsMatrix X * (olsMatrix X)ᵀ) * Cᵀ) by
      simp only [Matrix.mul_assoc], olsMatrix_mul_transpose hX,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hC), trace_one]
  have h := rank_eq_trace_of_mul_self (hypothesisMatrix_mul_self hX hC)
  rw [htr] at h
  exact_mod_cast h

/-- `H M = 0` for the hypothesis matrix `H` and the residual-maker matrix `M`. -/
theorem hypothesisMatrix_mul_residualMatrix {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) (C : Matrix r k ℝ) :
    hypothesisMatrix X C * residualMatrix X = 0 := by
  rw [hypothesisMatrix, Matrix.mul_assoc, olsMatrix_mul_residualMatrix hX, Matrix.mul_zero]

/-- **Central chi-square law of the linear-hypothesis numerator**: in `y = X β + ε` with
full-rank `X`, `σ > 0`, `σ⁻¹ ε` standard Gaussian, a full-row-rank `C` with `q = card r > 0`, and
under `H₀ : C β = c`,
`(C β̂ - c)ᵀ (C (Xᵀ X)⁻¹ Cᵀ)⁻¹ (C β̂ - c) / σ² ~ χ²_q`. -/
theorem hasLaw_linearHypothesis_numerator {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) (hr : 0 < Fintype.card r)
    (β : k → ℝ) {c : r → ℝ} (hβ : C *ᵥ β = c) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    HasLaw (fun ω => (C *ᵥ olsEstimator X (X *ᵥ β + ε ω) - c) ⬝ᵥ
        ((C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ *ᵥ (C *ᵥ olsEstimator X (X *ᵥ β + ε ω) - c)) / σ ^ 2)
      (chiSquareMeasure (Fintype.card r)) μ := by
  have hH : 0 < (hypothesisMatrix X C).rank := by rw [rank_hypothesisMatrix hX hC]; exact hr
  have hZ : HasLaw (fun ω => (σ⁻¹ • ε ω) ⬝ᵥ hypothesisMatrix X C *ᵥ (σ⁻¹ • ε ω))
      (chiSquareMeasure (Fintype.card r)) μ := by
    refine HasLaw.fun_comp (Y := fun x => x ⬝ᵥ hypothesisMatrix X C *ᵥ x) ⟨by fun_prop, ?_⟩ hε
    rw [pi_gaussianReal_map_dotProduct_mulVec (hypothesisMatrix_isHermitian X C)
      (hypothesisMatrix_mul_self hX hC) hH, rank_hypothesisMatrix hX hC]
  have hq : ∀ e : m → ℝ, e ⬝ᵥ hypothesisMatrix X C *ᵥ e = (C *ᵥ (olsMatrix X *ᵥ e)) ⬝ᵥ
      ((C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ *ᵥ (C *ᵥ (olsMatrix X *ᵥ e))) := by
    intro e
    rw [hypothesisMatrix, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose, dotProduct_mulVec, vecMul_transpose]
  convert hZ using 2 with ω
  obtain ⟨z, hz⟩ : ∃ z, ε ω = σ • z := ⟨σ⁻¹ • ε ω, (smul_inv_smul_eq hσ (ε ω)).symm⟩
  rw [hz, inv_smul_smul₀ hσ.ne', hq, olsEstimator_add hX, mulVec_add, hβ, add_sub_cancel_left]
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp

/-- **Independence of the numerator and the residual sum of squares**: the linear-hypothesis
numerator is independent of `‖y - X β̂‖² / σ²`, for every `C` and `c` (no `H₀` needed). -/
theorem indepFun_linearHypothesis_numerator_rss_div_sq {m k r : Type*} [Fintype m]
    [DecidableEq m] [Fintype k] [DecidableEq k] [Fintype r] [DecidableEq r]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ}
    (hX : IsUnit (Xᵀ * X)) (C : Matrix r k ℝ) (c : r → ℝ) (β : k → ℝ) {ε : Ω → m → ℝ}
    {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    IndepFun (fun ω => (C *ᵥ olsEstimator X (X *ᵥ β + ε ω) - c) ⬝ᵥ
        ((C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ *ᵥ (C *ᵥ olsEstimator X (X *ᵥ β + ε ω) - c)) / σ ^ 2)
      (fun ω => (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
        (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) / σ ^ 2) μ := by
  exact (indepFun_olsEstimator_rss_div_sq hX β hσ hε).comp
    (φ := fun b => (C *ᵥ b - c) ⬝ᵥ ((C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ *ᵥ (C *ᵥ b - c)) / σ ^ 2)
    (ψ := id) (by fun_prop) measurable_id

end MathlibExt.Probability.Statistics.LinearModel

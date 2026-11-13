/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Inference

/-!
# Exact `t` law for a single estimated coefficient (Atlas ST04.T03)

Specialization of the general contrast `t` law
`MathlibExt.Probability.Statistics.LinearModel.hasLaw_tStatistic` to the
coordinate contrast `a = Pi.single j 1`: the standardized estimated
coefficient `(β̂_j - β_j) / √((‖y - X β̂‖² / (n - p)) · [(Xᵀ X)⁻¹]_{jj})`
has Student's `t` law with `n - p` degrees of freedom. The closed-form
`t` density is NOT proved here; the law is the ratio law
`studentTMeasure`, as in the general contrast theorem.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

/-- The `t` statistic for a single coefficient `β_j`: the textbook form
`(β̂_j - β_j) / √((‖y - X β̂‖² / (n - p)) · [(Xᵀ X)⁻¹]_{jj})`. -/
noncomputable def coefficientTStatistic {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] (X : Matrix m k ℝ) (j : k) (β : k → ℝ) (y : m → ℝ) : ℝ :=
  (olsEstimator X y j - β j) /
    √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y) /
      ((Fintype.card m - Fintype.card k : ℕ) : ℝ)) * (Xᵀ * X)⁻¹ j j)

/-- The contrast variance of the coordinate contrast `Pi.single j 1` is the
`jj` diagonal entry of the inverse Gram matrix. -/
theorem contrastVariance_pi_single {m k : Type*} [Fintype m]
    [Fintype k] [DecidableEq k] (X : Matrix m k ℝ) (j : k) :
    contrastVariance X (Pi.single j 1) = (Xᵀ * X)⁻¹ j j := by
  unfold contrastVariance
  rw [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply]

/-- The coefficient `t` statistic is the general contrast `t` statistic
`tStatistic` at the coordinate contrast `Pi.single j 1`. -/
theorem coefficientTStatistic_eq_tStatistic {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] (X : Matrix m k ℝ) (j : k) (β : k → ℝ) (y : m → ℝ) :
    coefficientTStatistic X j β y = tStatistic X (Pi.single j 1) β y := by
  unfold coefficientTStatistic tStatistic
  rw [contrastVariance_pi_single, single_one_dotProduct, Pi.sub_apply]

/-- **Exact `t` law of a single estimated coefficient**: in `y = X β + ε`
with full-rank `X`, `p < n`, `σ > 0`, `σ⁻¹ ε` standard Gaussian, the
statistic `(β̂_j - β_j) / √((‖y - X β̂‖² / (n - p)) · [(Xᵀ X)⁻¹]_{jj})`
has Student's `t` law with `n - p` degrees of freedom. -/
theorem hasLaw_coefficientTStatistic {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ)
    (j : k) :
    HasLaw (fun ω => coefficientTStatistic X j β (X *ᵥ β + ε ω))
      (studentTMeasure (Fintype.card m - Fintype.card k)) μ := by
  have hfun : (fun ω => coefficientTStatistic X j β (X *ᵥ β + ε ω))
      = fun ω => tStatistic X (Pi.single j 1) β (X *ᵥ β + ε ω) := by
    funext ω
    exact coefficientTStatistic_eq_tStatistic X j β _
  rw [hfun]
  apply hasLaw_tStatistic hX hkm β hσ hε
  intro h0
  have h1 := congrFun h0 j
  simp at h1

end MathlibExt.Probability.Statistics.LinearModel

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.LinearHypothesis
public import MathlibExt.Probability.Statistics.LinearModel.Sampling
public import MathlibExt.Probability.Distributions.SnedecorF
public import Mathlib.Probability.HasLaw

/-!
# Exact `F` inference for a linear hypothesis in the Gaussian linear model

For a fixed full-rank design and a full-row-rank hypothesis matrix, the `F` statistic
for `C β = c` has Snedecor's `F` law with `(q, n - p)` degrees of freedom under `H₀`.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.LinearModel

open Matrix MeasureTheory ProbabilityTheory

/-- The `F` statistic for the linear hypothesis `C β = c`: the scaled ratio of the
hypothesis sum of squares to the residual sum of squares. -/
noncomputable def fStatistic {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    (X : Matrix m k ℝ) (C : Matrix r k ℝ) (c : r → ℝ) (y : m → ℝ) : ℝ :=
  ((C *ᵥ olsEstimator X y - c) ⬝ᵥ ((C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ *ᵥ (C *ᵥ olsEstimator X y - c)) /
    (Fintype.card r : ℝ)) /
    (((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
      ((Fintype.card m - Fintype.card k : ℕ) : ℝ))

/-- **Exact `F` law for a linear hypothesis**: in `y = X β + ε` with full-rank `X`,
`σ > 0`, `σ⁻¹ ε` standard Gaussian, a full-row-rank `C` with `0 < q = card r`,
`p < n`, and under `H₀ : C β = c`, the `F` statistic has Snedecor's `F` law with
`(q, n - p)` degrees of freedom. -/
theorem hasLaw_fStatistic {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) (hr : 0 < Fintype.card r)
    (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {c : r → ℝ} (hβ : C *ᵥ β = c) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    HasLaw (fun ω => fStatistic X C c (X *ᵥ β + ε ω))
      (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)) μ := by
  have hprob : IsProbabilityMeasure μ := hε.isProbabilityMeasure
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
  have hq : (Fintype.card r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hnp : 0 < Fintype.card m - Fintype.card k := Nat.sub_pos_of_lt hkm
  have hnp' : ((Fintype.card m - Fintype.card k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hnp.ne'
  have hU := hasLaw_linearHypothesis_numerator hX hC hr β hβ hσ hε
  have hV := hasLaw_rss_div_sq hX hkm β σ hσ hε
  have hI := indepFun_linearHypothesis_numerator_rss_div_sq hX C c β hσ hε
  have hmap := @map_div_chiSquare_eq_snedecorF _ _ _ hprob _ _ hr hnp _ _ hU hV hI
  have halg : ∀ a b : ℝ, (a / (Fintype.card r : ℝ)) /
        (b / ((Fintype.card m - Fintype.card k : ℕ) : ℝ))
      = (a / σ ^ 2 / (Fintype.card r : ℝ)) /
        (b / σ ^ 2 / ((Fintype.card m - Fintype.card k : ℕ) : ℝ)) := by
    intro a b
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    · rw [div_eq_div_iff (div_ne_zero hb hnp')
        (div_ne_zero (div_ne_zero hb hσ2) hnp')]
      field_simp
  have hfun : (fun ω => fStatistic X C c (X *ᵥ β + ε ω))
      = fun ω => ((C *ᵥ olsEstimator X (X *ᵥ β + ε ω) - c) ⬝ᵥ
          ((C * (Xᵀ * X)⁻¹ * Cᵀ)⁻¹ *ᵥ (C *ᵥ olsEstimator X (X *ᵥ β + ε ω) - c)) /
          σ ^ 2 / (Fintype.card r : ℝ)) /
        (((X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
          (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) / σ ^ 2) /
          ((Fintype.card m - Fintype.card k : ℕ) : ℝ)) := by
    funext ω
    simp only [fStatistic]
    exact halg _ _
  rw [hfun]
  exact ⟨(hU.aemeasurable.div_const _).div (hV.aemeasurable.div_const _), hmap⟩

end MathlibExt.Probability.Statistics.LinearModel

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Inference
public import MathlibExt.Probability.Statistics.LinearModel.LinearHypothesis
public import MathlibExt.Probability.Statistics.LinearModel.Sampling
public import MathlibExt.Probability.Distributions.SnedecorF
public import MathlibExt.Probability.Distributions.ChiSquare
public import Mathlib.Probability.HasLaw

/-!
# Exact `F` and single-contrast `T ^ 2` inference in the Gaussian linear model

For a fixed full-rank design and a full-row-rank hypothesis matrix, the `F` statistic
for `C β = c` has Snedecor's `F` law with `(q, n - p)` degrees of freedom under `H₀`.
For a nonzero contrast, the squared `t` statistic has `F(1, n - p)` law, agreeing pointwise
with the rank-one case.
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

private theorem tsq_dotProduct_self_nonneg {m : Type*} [Fintype m] (x : m → ℝ) :
    0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

private theorem tsq_contrastVariance_zero {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq k] (X : Matrix m k ℝ) : contrastVariance X 0 = 0 := by
  classical
  simp [contrastVariance, dotProduct]

private theorem tsq_contrastVariance_nonneg {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq k] (X : Matrix m k ℝ) (a : k → ℝ) : 0 ≤ contrastVariance X a := by
  classical
  by_cases hX : IsUnit (Xᵀ * X)
  · by_cases ha : a = 0
    · simp [ha, tsq_contrastVariance_zero]
    · exact (contrastVariance_pos hX ha).le
  · have hdet : (Xᵀ * X).det = 0 := by
      by_contra h
      exact hX ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
    have hG0 : (Xᵀ * X)⁻¹ = 0 := by
      rw [Matrix.inv_def, hdet, Ring.inverse_zero, zero_smul]
    have hq0 : contrastVariance X a = 0 := by
      simp [contrastVariance, hG0, dotProduct]
    simp [hq0]

private theorem tsq_sq_div_sqrt (u v d : ℝ) (h : 0 ≤ v / d) :
    (u / √(v / d)) ^ 2 = (u ^ 2 / ((1 : ℕ) : ℝ)) / (v / d) := by
  rw [div_pow, Real.sq_sqrt h, Nat.cast_one, div_one]

private theorem tsq_agree_real (N A q : ℝ) (hA : 0 ≤ A) (hq : 0 ≤ q) :
    (N / √(A * q)) ^ 2 = (N ^ 2 / q) / A := by
  have hS : 0 ≤ A * q := mul_nonneg hA hq
  rw [div_pow, Real.sq_sqrt hS, div_div, mul_comm A q]

private theorem tsq_single_gram {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq k] (X : Matrix m k ℝ) (a : k → ℝ) :
    (Matrix.of fun _ : Fin 1 => a) * (Xᵀ * X)⁻¹ * (Matrix.of fun _ : Fin 1 => a)ᵀ
      = Matrix.of fun _ _ : Fin 1 => contrastVariance X a := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, contrastVariance,
    dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k' _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem tsq_inv_one_one (q : ℝ) :
    (Matrix.of fun (_ _ : Fin 1) => q)⁻¹ = Matrix.of fun (_ _ : Fin 1) => q⁻¹ := by
  have hdet : (Matrix.of fun (_ _ : Fin 1) => q).det = q := by
    simp only [Matrix.det_fin_one, Matrix.of_apply]
  rw [Matrix.inv_def, Matrix.adjugate_fin_one, hdet, Ring.inverse_eq_inv]
  ext i j
  fin_cases i; fin_cases j; simp [Matrix.of_apply]

/-- **Single-contrast `F` law**: the squared contrast `t` statistic has Snedecor's `F`
law with `(1, n - p)` degrees of freedom. -/
theorem hasLaw_tStatistic_sq {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ)
    {a : k → ℝ} (ha : a ≠ 0) :
    HasLaw (fun ω => (tStatistic X a β (X *ᵥ β + ε ω)) ^ 2)
      (snedecorFMeasure 1 (Fintype.card m - Fintype.card k)) μ := by
  have := hε.isProbabilityMeasure
  have hq := contrastVariance_pos hX ha
  have hU := hasLaw_contrast_div hX β hσ hε ha
  have hV := hasLaw_rss_div_sq hX hkm β σ hσ hε
  have hUV := (indepFun_olsEstimator_rss_div_sq hX β hσ hε).comp
    (φ := fun b => a ⬝ᵥ (b - β) / (σ * √(contrastVariance X a))) (ψ := id)
    (by fun_prop) measurable_id
  have hU2 : HasLaw
      (fun ω => (a ⬝ᵥ (olsEstimator X (X *ᵥ β + ε ω) - β) /
        (σ * √(contrastVariance X a))) ^ 2)
      (chiSquareMeasure 1) μ :=
    HasLaw.fun_comp (Y := fun x : ℝ => x ^ 2)
      (⟨by fun_prop, gaussianReal_map_sq⟩ :
        HasLaw (fun x : ℝ => x ^ 2) (chiSquareMeasure 1) (gaussianReal 0 1)) hU
  have hUV2 := hUV.comp (φ := fun u : ℝ => u ^ 2) (ψ := id) (by fun_prop) measurable_id
  have hdf : 0 < Fintype.card m - Fintype.card k := by omega
  have hfun : ∀ ω, (tStatistic X a β (X *ᵥ β + ε ω)) ^ 2 =
      ((a ⬝ᵥ (olsEstimator X (X *ᵥ β + ε ω) - β) / (σ * √(contrastVariance X a))) ^ 2 /
        ((1 : ℕ) : ℝ)) /
        (((X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
          (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) / σ ^ 2) /
          ((Fintype.card m - Fintype.card k : ℕ) : ℝ)) := by
    intro ω
    rw [tStatistic_eq_div_sqrt a β _ hσ hq.le]
    apply tsq_sq_div_sqrt
    have hrss := tsq_dotProduct_self_nonneg
      (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω))
    positivity
  simp only [hfun]
  exact ⟨(hU2.aemeasurable.div_const _).div (hV.aemeasurable.div_const _),
    map_div_chiSquare_eq_snedecorF one_pos hdf hU2 hV hUV2⟩

/-- Rank-one agreement: the squared single-contrast `t` statistic equals the `F`
statistic for the single-row hypothesis matrix holding `a`. -/
theorem tStatistic_sq_eq_fStatistic {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (a β : k → ℝ) (y : m → ℝ) :
    (tStatistic X a β y) ^ 2 =
      fStatistic X (Matrix.of fun _ : Fin 1 => a) (fun _ => a ⬝ᵥ β) y := by
  have hqnn : 0 ≤ contrastVariance X a := tsq_contrastVariance_nonneg X a
  have hrss : 0 ≤ (y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y) :=
    tsq_dotProduct_self_nonneg _
  have hAnn : 0 ≤ ((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
      ((Fintype.card m - Fintype.card k : ℕ) : ℝ) :=
    div_nonneg hrss (Nat.cast_nonneg _)
  have hsum1 : ∀ f : Fin 1 → ℝ, ∑ i, f i = f 0 := by
    intro f
    have huniv : (Finset.univ : Finset (Fin 1)) = {0} := by decide
    rw [huniv, Finset.sum_singleton]
  have hw : ∀ i : Fin 1, ((Matrix.of fun _ : Fin 1 => a) *ᵥ olsEstimator X y -
      (fun _ : Fin 1 => a ⬝ᵥ β)) i = a ⬝ᵥ (olsEstimator X y - β) := by
    intro i
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_sub,
      Finset.sum_sub_distrib]
  have hG : (Matrix.of fun _ : Fin 1 => a) * (Xᵀ * X)⁻¹ * (Matrix.of fun _ : Fin 1 => a)ᵀ
      = Matrix.of fun _ _ : Fin 1 => contrastVariance X a :=
    tsq_single_gram X a
  have hGi : (Matrix.of fun _ _ : Fin 1 => contrastVariance X a)⁻¹
      = Matrix.of fun (_ _ : Fin 1) => (contrastVariance X a)⁻¹ :=
    tsq_inv_one_one _
  have hQi : ∀ i : Fin 1, ((Matrix.of fun (_ _ : Fin 1) => (contrastVariance X a)⁻¹) *ᵥ
      ((Matrix.of fun _ : Fin 1 => a) *ᵥ olsEstimator X y - (fun _ : Fin 1 => a ⬝ᵥ β))) i
      = (contrastVariance X a)⁻¹ * (a ⬝ᵥ (olsEstimator X y - β)) := by
    intro i
    simp only [Matrix.mulVec, Matrix.of_apply]
    change ∑ j, (contrastVariance X a)⁻¹ * (((Matrix.of fun _ : Fin 1 => a) *ᵥ olsEstimator X y -
      (fun _ : Fin 1 => a ⬝ᵥ β)) j) = (contrastVariance X a)⁻¹ * (a ⬝ᵥ (olsEstimator X y - β))
    rw [hsum1, hw]
  have hQ : ((Matrix.of fun _ : Fin 1 => a) *ᵥ olsEstimator X y - (fun _ : Fin 1 => a ⬝ᵥ β)) ⬝ᵥ
      ((Matrix.of fun (_ _ : Fin 1) => (contrastVariance X a)⁻¹) *ᵥ
        ((Matrix.of fun _ : Fin 1 => a) *ᵥ olsEstimator X y - (fun _ : Fin 1 => a ⬝ᵥ β)))
      = (a ⬝ᵥ (olsEstimator X y - β)) ^ 2 / contrastVariance X a := by
    change ∑ i, (((Matrix.of fun _ : Fin 1 => a) *ᵥ olsEstimator X y -
      (fun _ : Fin 1 => a ⬝ᵥ β)) i *
      (((Matrix.of fun (_ _ : Fin 1) => (contrastVariance X a)⁻¹) *ᵥ
        ((Matrix.of fun _ : Fin 1 => a) *ᵥ olsEstimator X y - (fun _ : Fin 1 => a ⬝ᵥ β))) i)) =
      (a ⬝ᵥ (olsEstimator X y - β)) ^ 2 / contrastVariance X a
    rw [hsum1, hw, hQi]
    ring
  simp only [tStatistic, fStatistic, hG, hGi, hQ, Fintype.card_fin, Nat.cast_one, div_one]
  exact tsq_agree_real _ _ _ hAnn hqnn

end MathlibExt.Probability.Statistics.LinearModel

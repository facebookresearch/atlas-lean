/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.TangencyPortfolio
import Mathlib.Algebra.Order.Star.Real

/-!
# The CAPM security market line

In a one-period mean-variance market with a risk-free return `r`, risky expected returns `μ` and
a positive definite covariance matrix `S`, suppose the market portfolio `wM` is fully invested, has
a positive risk premium `μᵀ wM - r`, and is efficient in the tangency sense: no fully invested
portfolio has a larger Sharpe ratio
(`MathlibExt.Probability.Finance.TangencyPortfolio.sharpeRatio`).
Then every asset lies on the security market line `μ i - r = β_i (μᵀ wM - r)`, where
`β_i = (S wM)_i / (wMᵀ S wM)` is the covariance of asset `i` with the market over the market
variance. The proof is the first-order condition of Sharpe maximality along fully invested
perturbations `wM + t d` with `∑ d = 0`.

The statement is at the level of the covariance matrix: the identification of `(S wM)_i` with
`Cov(R_i, R_M)` for random returns, and empirical beta estimation, are separate.

## Main results

* `beta`: the beta of an asset with respect to a portfolio.
* `securityMarketLine`: the security market line for a Sharpe-efficient market portfolio.

## References

* W. F. Sharpe, *Capital asset prices: a theory of market equilibrium under conditions of risk*,
  J. Finance 19 (1964), 425–442.
* J. Lintner, *The valuation of risk assets and the selection of risky investments in stock
  portfolios and capital budgets*, Rev. Econ. Stat. 47 (1965), 13–37.
* M. Haugh, *Mean-Variance Optimization and the CAPM*, IEOR E4706 lecture notes, Columbia
  University (2016).
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.CAPM

open Matrix MathlibExt.Probability.Finance.TangencyPortfolio

/-- The beta `(S w_M)_i / (w_Mᵀ S w_M)` of asset `i` with respect to the portfolio `w_M`: the
covariance of asset `i`'s return with the portfolio return divided by the portfolio variance,
when `S` is the covariance matrix of the asset returns. -/
noncomputable def beta {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (wM : ι → ℝ) (i : ι) : ℝ :=
  (S *ᵥ wM) i / (wM ⬝ᵥ (S *ᵥ wM))

/-- First-order vanishing: if `2 * t * L ≤ t ^ 2 * R` for all `t` near `0`, then `L = 0`. -/
private theorem quadFirstOrder (L R δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : ∀ t : ℝ, |t| < δ₀ → 2 * t * L ≤ t ^ 2 * R) : L = 0 := by
  by_contra hL
  have hL1 : (0 : ℝ) < |L| + 1 := by
    have := abs_nonneg L
    linarith
  have hR1 : (0 : ℝ) < |R| + 1 := by
    have := abs_nonneg R
    linarith
  set u : ℝ := min (δ₀ / (|L| + 1)) (1 / (|R| + 1)) with hu_def
  have hu_pos : 0 < u := lt_min (div_pos hδ hL1) (div_pos zero_lt_one hR1)
  have hu_le_L : u ≤ δ₀ / (|L| + 1) := min_le_left _ _
  have hu_le_R : u ≤ 1 / (|R| + 1) := min_le_right _ _
  have hut : |L * u| < δ₀ := by
    have h1 : |L| * u ≤ |L| * (δ₀ / (|L| + 1)) :=
      mul_le_mul_of_nonneg_left hu_le_L (abs_nonneg _)
    have h2 : |L| * (δ₀ / (|L| + 1)) < δ₀ := by
      have heq : |L| * (δ₀ / (|L| + 1)) = (|L| * δ₀) / (|L| + 1) := by ring
      rw [heq, div_lt_iff₀ hL1]
      nlinarith [hδ, abs_nonneg L]
    rw [abs_mul, abs_of_pos hu_pos]
    linarith
  have h2 := h (L * u) hut
  have hL2 : (0 : ℝ) < L ^ 2 := sq_pos_of_ne_zero hL
  have hcan : (2 : ℝ) * u ≤ u ^ 2 * R := by
    have h' : L ^ 2 * (2 * u) ≤ L ^ 2 * (u ^ 2 * R) := by linear_combination h2
    exact le_of_mul_le_mul_left h' hL2
  have hfin : (2 : ℝ) ≤ u * R := by
    have h'' : u * 2 ≤ u * (u * R) := by linear_combination hcan
    exact le_of_mul_le_mul_left h'' hu_pos
  have hfin2 : (2 : ℝ) ≤ |u * R| := le_trans hfin (le_abs_self _)
  have habs : |u * R| = u * |R| := by rw [abs_mul, abs_of_pos hu_pos]
  have h4 : u * |R| ≤ (1 / (|R| + 1)) * |R| :=
    mul_le_mul_of_nonneg_right hu_le_R (abs_nonneg _)
  have h5 : (1 / (|R| + 1)) * |R| < 1 := by
    have heq : (1 / (|R| + 1)) * |R| = |R| / (|R| + 1) := by ring
    rw [heq, div_lt_one hR1]
    have := abs_nonneg R
    linarith
  rw [habs] at hfin2
  linarith

/-- **Security market line (CAPM).** Let `S` be a positive definite covariance matrix of asset
returns, `μ` the expected returns and `r` the risk-free return. Suppose the market portfolio `wM`
is fully invested, has a positive risk premium `μᵀ wM - r > 0`, and is mean-variance efficient in
the tangency sense: no fully invested portfolio has a larger Sharpe ratio. Then every asset
satisfies `μ i - r = β_i (μᵀ wM - r)`. -/
theorem securityMarketLine {ι : Type*} [Fintype ι] {S : Matrix ι ι ℝ} (hS : S.PosDef)
    (μ : ι → ℝ) (r : ℝ) {wM : ι → ℝ} (hwM : ∑ i, wM i = 1) (hprem : 0 < μ ⬝ᵥ wM - r)
    (heff : ∀ w : ι → ℝ, ∑ i, w i = 1 → sharpeRatio S μ r w ≤ sharpeRatio S μ r wM)
    (i : ι) :
    μ i - r = beta S wM i * (μ ⬝ᵥ wM - r) := by
  let _ : DecidableEq ι := fun a b => Classical.propDecidable (a = b)
  have hwMne : wM ≠ 0 := by
    intro hcon
    have h0 : ∑ k, wM k = 0 := by
      rw [hcon]
      simp
    rw [hwM] at h0
    exact one_ne_zero h0
  have hσ2 : (0 : ℝ) < wM ⬝ᵥ (S *ᵥ wM) := by
    have h := hS.dotProduct_mulVec_pos hwMne
    rwa [star_trivial] at h
  have hST : Sᵀ = S :=
    (conjTranspose_eq_transpose_of_trivial S).symm.trans hS.isHermitian
  have hswap : ∀ d : ι → ℝ, d ⬝ᵥ (S *ᵥ wM) = wM ⬝ᵥ (S *ᵥ d) := by
    intro d
    have hmul : d ᵥ* S = S *ᵥ d := by
      have h1 : d ᵥ* S = Sᵀ *ᵥ d := (mulVec_transpose S d).symm
      rw [h1, hST]
    rw [dotProduct_mulVec, hmul, dotProduct_comm]
  have foc : ∀ d : ι → ℝ, ∑ k, d k = 0 →
      (wM ⬝ᵥ (S *ᵥ wM)) * (μ ⬝ᵥ d) = (μ ⬝ᵥ wM - r) * (wM ⬝ᵥ (S *ᵥ d)) := by
    intro d hd
    have hexpand_lin : ∀ t : ℝ, μ ⬝ᵥ (wM + t • d) = μ ⬝ᵥ wM + t * (μ ⬝ᵥ d) := by
      intro t
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hexpand_quad : ∀ t : ℝ, (wM + t • d) ⬝ᵥ (S *ᵥ (wM + t • d))
        = (wM ⬝ᵥ (S *ᵥ wM)) + 2 * t * (wM ⬝ᵥ (S *ᵥ d)) + t ^ 2 * (d ⬝ᵥ (S *ᵥ d)) := by
      intro t
      have hSw : S *ᵥ (wM + t • d) = S *ᵥ wM + t • (S *ᵥ d) := by
        rw [mulVec_add, mulVec_smul]
      simp only [hSw, add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      rw [hswap d]
      ring
    have hδ₀ : (0 : ℝ) < (μ ⬝ᵥ wM - r) / (|μ ⬝ᵥ d| + 1) := by
      apply div_pos hprem
      have := abs_nonneg (μ ⬝ᵥ d)
      linarith
    have hper : ∀ t : ℝ, |t| < (μ ⬝ᵥ wM - r) / (|μ ⬝ᵥ d| + 1) →
        2 * t * ((μ ⬝ᵥ wM - r) * (μ ⬝ᵥ d) * (wM ⬝ᵥ (S *ᵥ wM))
          - (μ ⬝ᵥ wM - r) ^ 2 * (wM ⬝ᵥ (S *ᵥ d)))
        ≤ t ^ 2 * ((μ ⬝ᵥ wM - r) ^ 2 * (d ⬝ᵥ (S *ᵥ d))
          - (μ ⬝ᵥ d) ^ 2 * (wM ⬝ᵥ (S *ᵥ wM))) := by
      intro t ht
      have hsumw : ∑ k, (wM + t • d) k = 1 := by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        have e2 : (∑ k, (t • d) k) = t * (∑ k, d k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [Pi.smul_apply, smul_eq_mul]
        rw [e2, hd, mul_zero, hwM, add_zero]
      have hsharp := heff (wM + t • d) hsumw
      unfold sharpeRatio at hsharp
      rw [hexpand_lin t] at hsharp
      have hpos1 : (0 : ℝ) < μ ⬝ᵥ wM + t * (μ ⬝ᵥ d) - r := by
        have hb1 : (0 : ℝ) < |μ ⬝ᵥ d| + 1 := by
          have := abs_nonneg (μ ⬝ᵥ d)
          linarith
        have hle : |t| * |μ ⬝ᵥ d|
            ≤ ((μ ⬝ᵥ wM - r) / (|μ ⬝ᵥ d| + 1)) * |μ ⬝ᵥ d| :=
          mul_le_mul_of_nonneg_right ht.le (abs_nonneg _)
        have hlt : ((μ ⬝ᵥ wM - r) / (|μ ⬝ᵥ d| + 1)) * |μ ⬝ᵥ d| < μ ⬝ᵥ wM - r := by
          have heq : ((μ ⬝ᵥ wM - r) / (|μ ⬝ᵥ d| + 1)) * |μ ⬝ᵥ d|
              = (μ ⬝ᵥ wM - r) * (|μ ⬝ᵥ d| / (|μ ⬝ᵥ d| + 1)) := by ring
          rw [heq]
          have hfrac : |μ ⬝ᵥ d| / (|μ ⬝ᵥ d| + 1) < 1 := by
            rw [div_lt_one hb1]
            have := abs_nonneg (μ ⬝ᵥ d)
            linarith
          have hmul := mul_lt_mul_of_pos_left hfrac hprem
          rwa [mul_one] at hmul
        have habs : |t * (μ ⬝ᵥ d)| < μ ⬝ᵥ wM - r := by
          rw [abs_mul]
          linarith
        have hneg := neg_lt_of_abs_lt habs
        linarith
      have hwne : wM + t • d ≠ 0 := by
        intro hcon
        have h0 : ∑ k, (wM + t • d) k = 0 := by
          rw [hcon]
          simp
        rw [hsumw] at h0
        exact one_ne_zero h0
      have hQ : (0 : ℝ) < (wM + t • d) ⬝ᵥ (S *ᵥ (wM + t • d)) := by
        have h := hS.dotProduct_mulVec_pos hwne
        rwa [star_trivial] at h
      have hsqrtQ : (0 : ℝ) < Real.sqrt ((wM + t • d) ⬝ᵥ (S *ᵥ (wM + t • d))) :=
        Real.sqrt_pos.mpr hQ
      have hsqrtS : (0 : ℝ) < Real.sqrt (wM ⬝ᵥ (S *ᵥ wM)) := Real.sqrt_pos.mpr hσ2
      have hstep1 : ((μ ⬝ᵥ wM + t * (μ ⬝ᵥ d) - r)
          / Real.sqrt ((wM + t • d) ⬝ᵥ (S *ᵥ (wM + t • d))))
          * Real.sqrt (wM ⬝ᵥ (S *ᵥ wM)) ≤ μ ⬝ᵥ wM - r :=
        (le_div_iff₀ hsqrtS).mp hsharp
      have hstep2 : ((μ ⬝ᵥ wM + t * (μ ⬝ᵥ d) - r) * Real.sqrt (wM ⬝ᵥ (S *ᵥ wM)))
          / Real.sqrt ((wM + t • d) ⬝ᵥ (S *ᵥ (wM + t • d))) ≤ μ ⬝ᵥ wM - r := by
        rwa [div_mul_eq_mul_div] at hstep1
      have hcross : (μ ⬝ᵥ wM + t * (μ ⬝ᵥ d) - r) * Real.sqrt (wM ⬝ᵥ (S *ᵥ wM))
          ≤ (μ ⬝ᵥ wM - r) * Real.sqrt ((wM + t • d) ⬝ᵥ (S *ᵥ (wM + t • d))) :=
        (div_le_iff₀ hsqrtQ).mp hstep2
      have hsq0 : (μ ⬝ᵥ wM + t * (μ ⬝ᵥ d) - r) ^ 2 * (wM ⬝ᵥ (S *ᵥ wM))
          ≤ (μ ⬝ᵥ wM - r) ^ 2 * ((wM + t • d) ⬝ᵥ (S *ᵥ (wM + t • d))) := by
        have hn1 : (0 : ℝ)
            ≤ (μ ⬝ᵥ wM + t * (μ ⬝ᵥ d) - r) * Real.sqrt (wM ⬝ᵥ (S *ᵥ wM)) :=
          mul_nonneg hpos1.le (Real.sqrt_nonneg _)
        have hn2 : (0 : ℝ)
            ≤ (μ ⬝ᵥ wM - r) * Real.sqrt ((wM + t • d) ⬝ᵥ (S *ᵥ (wM + t • d))) :=
          mul_nonneg hprem.le (Real.sqrt_nonneg _)
        have hsq := sq_le_sq'
          (a := (μ ⬝ᵥ wM + t * (μ ⬝ᵥ d) - r) * Real.sqrt (wM ⬝ᵥ (S *ᵥ wM)))
          (b := (μ ⬝ᵥ wM - r) * Real.sqrt ((wM + t • d) ⬝ᵥ (S *ᵥ (wM + t • d))))
          (by linarith) hcross
        rw [mul_pow, mul_pow, Real.sq_sqrt hσ2.le, Real.sq_sqrt hQ.le] at hsq
        exact hsq
      rw [hexpand_quad t] at hsq0
      linear_combination hsq0
    have hL0 := quadFirstOrder _ _ _ hδ₀ hper
    have hcan : (μ ⬝ᵥ wM - r) * ((μ ⬝ᵥ d) * (wM ⬝ᵥ (S *ᵥ wM)))
        = (μ ⬝ᵥ wM - r) * ((μ ⬝ᵥ wM - r) * (wM ⬝ᵥ (S *ᵥ d))) := by
      linear_combination hL0
    have hcancel := mul_left_cancel₀ (ne_of_gt hprem) hcan
    linear_combination hcancel
  set vv : ι → ℝ := (wM ⬝ᵥ (S *ᵥ wM)) • μ - ((wM ⬝ᵥ (S *ᵥ wM)) * r) • (1 : ι → ℝ)
    - (μ ⬝ᵥ wM - r) • (S *ᵥ wM) with hvv_def
  have hall : ∀ k, vv k = vv i := by
    intro k
    by_cases hki : k = i
    · rw [hki]
    · have hsum : ∑ l, ((Pi.single i (1 : ℝ) - Pi.single k (1 : ℝ)) : ι → ℝ) l = 0 := by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, Fintype.sum_pi_single', sub_self]
      have hfoc := foc (Pi.single i (1 : ℝ) - Pi.single k (1 : ℝ)) hsum
      have hdk : μ ⬝ᵥ (Pi.single i (1 : ℝ) - Pi.single k (1 : ℝ)) = μ i - μ k := by
        simp only [dotProduct_sub, dotProduct_single_one]
      have hqk : wM ⬝ᵥ (S *ᵥ (Pi.single i (1 : ℝ) - Pi.single k (1 : ℝ)))
          = (S *ᵥ wM) i - (S *ᵥ wM) k := by
        rw [← hswap, sub_dotProduct]
        simp only [single_one_dotProduct]
      rw [hdk, hqk] at hfoc
      simp only [hvv_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
      linear_combination -hfoc
  have hsum_v : wM ⬝ᵥ vv = vv i := by
    have hcongr : wM ⬝ᵥ vv = ∑ k, wM k * vv i := by
      change (∑ k, wM k * vv k) = ∑ k, wM k * vv i
      apply Finset.sum_congr rfl
      intro k _
      rw [hall k]
    rw [hcongr, ← Finset.sum_mul, hwM, one_mul]
  have h1 : wM ⬝ᵥ (1 : ι → ℝ) = 1 := by
    change (∑ k, wM k * (1 : ι → ℝ) k) = 1
    simp [hwM]
  have hzero : wM ⬝ᵥ vv = 0 := by
    rw [hvv_def]
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm wM μ, h1]
    ring
  rw [hsum_v] at hzero
  have hσ2ne : (wM ⬝ᵥ (S *ᵥ wM)) ≠ 0 := ne_of_gt hσ2
  have key : (wM ⬝ᵥ (S *ᵥ wM)) * (μ i - r) = (μ ⬝ᵥ wM - r) * (S *ᵥ wM) i := by
    rw [hvv_def] at hzero
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one] at hzero
    linear_combination hzero
  unfold beta
  rw [div_mul_eq_mul_div, eq_div_iff hσ2ne]
  linear_combination key

end MathlibExt.Probability.Finance.CAPM

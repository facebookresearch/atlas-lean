/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Star.Real

/-!
# The tangency portfolio maximizes the Sharpe ratio

Assets are indexed by a finite type `ι`, `S` is the positive definite covariance matrix of their
returns, `μ` the expected returns and `r` the risk-free return. The Sharpe ratio of a portfolio
`w` is `(μᵀ w - r) / √(wᵀ S w)`. The tangency direction is `z = S⁻¹ (μ - r 1)`; when `1ᵀ z ≠ 0`
it normalizes to the fully invested tangency portfolio `z / (1ᵀ z)`. Its orientation is set by
`1ᵀ z = 1ᵀ S⁻¹ μ - r · 1ᵀ S⁻¹ 1`, which is positive iff `r` is below
`μ_GMV = (1ᵀ S⁻¹ μ) / (1ᵀ S⁻¹ 1)`, the expected return of the global minimum-variance portfolio.

## Main results

* `sum_tangencyDirection`, `sum_tangencyDirection_pos_iff`: the orientation identity and sign.
* `sum_tangencyPortfolio`: the normalized tangency portfolio is fully invested.
* `sharpeRatio_tangencyPortfolio`: for `r < μ_GMV` its Sharpe ratio is
  `√((μ - r 1)ᵀ S⁻¹ (μ - r 1))`.
* `sharpeRatio_le_sharpeRatio_tangencyPortfolio`: for `r < μ_GMV` it maximizes the Sharpe ratio
  over fully invested portfolios.
* `sharpeRatio_tangencyPortfolio_le_of_lt`: for `μ_GMV < r` it minimizes the Sharpe ratio.

## References

* M. Haugh, *Mean-Variance Optimization and the CAPM*, IEOR E4706 lecture notes, Columbia
  University (2016): the tangency portfolio is the risky portfolio with weights proportional to
  `S⁻¹ (μ - r 1)`, scaled to sum to one, and it is the Sharpe-optimal portfolio.
* R. C. Merton, *An analytic derivation of the efficient portfolio frontier*, J. Financial
  Quant. Anal. 7 (1972), 1851–1872: the global minimum-variance return `μ_GMV`.
* W. F. Sharpe, *Mutual fund performance*, J. Business 39 (1966), 119–138: the Sharpe ratio.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.TangencyPortfolio

open Matrix
open MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence (quadForm)

/-- The Sharpe ratio `(μᵀ w - r) / √(wᵀ S w)` of the portfolio `w`, for expected asset returns
`μ`, covariance matrix `S` and risk-free return `r`. -/
noncomputable def sharpeRatio {ι : Type*} [Fintype ι] (S : Matrix ι ι ℝ) (μ : ι → ℝ) (r : ℝ)
    (w : ι → ℝ) : ℝ :=
  (μ ⬝ᵥ w - r) / Real.sqrt (quadForm S w)

/-- The unnormalized tangency direction `z = S⁻¹ (μ - r 1)`. -/
noncomputable def tangencyDirection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (μ : ι → ℝ) (r : ℝ) : ι → ℝ :=
  S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))

/-- The fully invested tangency portfolio `z / (1ᵀ z)`; it is normalizable when `1ᵀ z ≠ 0`. -/
noncomputable def tangencyPortfolio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (μ : ι → ℝ) (r : ℝ) : ι → ℝ :=
  (∑ i, tangencyDirection S μ r i)⁻¹ • tangencyDirection S μ r

/-- Orientation identity: `1ᵀ z = 1ᵀ S⁻¹ μ - r · 1ᵀ S⁻¹ 1`, i.e. `C (μ_GMV - r)` with
`C = 1ᵀ S⁻¹ 1` and `μ_GMV = (1ᵀ S⁻¹ μ) / C` the expected return of the global
minimum-variance portfolio. -/
theorem sum_tangencyDirection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (μ : ι → ℝ) (r : ℝ) :
    ∑ i, tangencyDirection S μ r i =
      (1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ) - r * ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1)) := by
  unfold tangencyDirection
  have h1 : (∑ i, (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) i) =
      (1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) := by
    simp [dotProduct]
  rw [h1]
  rw [mulVec_sub]
  rw [dotProduct_sub]
  rw [Matrix.mulVec_smul]
  rw [dotProduct_smul]
  simp [smul_eq_mul]

/-- Orientation: the tangency direction has positive total weight iff the risk-free return is
below `μ_GMV = (1ᵀ S⁻¹ μ) / (1ᵀ S⁻¹ 1)`. -/
theorem sum_tangencyDirection_pos_iff {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (μ : ι → ℝ) (r : ℝ) :
    0 < ∑ i, tangencyDirection S μ r i ↔
      r < ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ)) / ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1)) := by
  have h1ne : (1 : ι → ℝ) ≠ 0 := by
    intro hcon
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hi := congrFun hcon i
    simp at hi
  have hC : 0 < (1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1) := by
    have h := hS.inv.dotProduct_mulVec_pos h1ne
    simpa using h
  rw [sum_tangencyDirection, lt_div_iff₀ hC, sub_pos]

/-- Normalization: when `1ᵀ z ≠ 0` the tangency portfolio is fully invested. -/
theorem sum_tangencyPortfolio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (μ : ι → ℝ) (r : ℝ) (h : ∑ i, tangencyDirection S μ r i ≠ 0) :
    ∑ i, tangencyPortfolio S μ r i = 1 := by
  unfold tangencyPortfolio
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀ h]

private theorem mulVec_inv_mulVec_cancel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (e : ι → ℝ) :
    S *ᵥ (S⁻¹ *ᵥ e) = e := by
  have hU : IsUnit S := hS.isUnit
  have hdet : IsUnit S.det := (isUnit_iff_isUnit_det S).mp hU
  have hSS : S * S⁻¹ = 1 := mul_nonsing_inv S hdet
  have hmul : S *ᵥ (S⁻¹ *ᵥ e) = (S * S⁻¹) *ᵥ e := mulVec_mulVec e S S⁻¹
  rw [hmul, hSS, one_mulVec]

private theorem pos_quad_of_posDef {ι : Type*} [Fintype ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) {x : ι → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (S *ᵥ x) := by
  have h := hS.dotProduct_mulVec_pos hx
  simpa using h

private theorem sum_eq_dotProduct_one {ι : Type*} [Fintype ι]
    (w : ι → ℝ) : ∑ i, w i = (1 : ι → ℝ) ⬝ᵥ w := by
  simp [dotProduct]

private theorem excess_eq_of_sum_one {ι : Type*} [Fintype ι]
    (μ w : ι → ℝ) (r : ℝ) (hw : ∑ i, w i = 1) :
    μ ⬝ᵥ w - r = (μ - r • (1 : ι → ℝ)) ⬝ᵥ w := by
  have h1w : (1 : ι → ℝ) ⬝ᵥ w = 1 := by
    rw [← sum_eq_dotProduct_one]
    exact hw
  rw [sub_dotProduct, smul_dotProduct, h1w, smul_eq_mul, mul_one]

private theorem excess_ne_zero_of_ne {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (μ : ι → ℝ) {r : ℝ}
    (hr : r ≠ ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ)) / ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1))) :
    (μ - r • (1 : ι → ℝ)) ≠ 0 := by
  intro he
  have hμ : μ = r • (1 : ι → ℝ) := sub_eq_zero.mp he
  have h1ne : (1 : ι → ℝ) ≠ (0 : ι → ℝ) := by
    intro hcon
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hi := congrFun hcon i
    simp at hi
  have hC : 0 < (1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1) := by
    have h := hS.inv.dotProduct_mulVec_pos h1ne
    simpa using h
  have hCne : ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1)) ≠ 0 := ne_of_gt hC
  have hA : (1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ) = r * ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1)) := by
    rw [hμ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hdiv : ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ)) / ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1)) = r := by
    rw [hA, mul_div_cancel_right₀ _ hCne]
  exact hr hdiv.symm

/-- The Sharpe ratio of the tangency portfolio is `√((μ - r 1)ᵀ S⁻¹ (μ - r 1))` when the
risk-free return is below `μ_GMV`. -/
theorem sharpeRatio_tangencyPortfolio {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (μ : ι → ℝ) {r : ℝ}
    (hr : r < ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ)) / ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1))) :
    sharpeRatio S μ r (tangencyPortfolio S μ r) =
      Real.sqrt (quadForm S⁻¹ (μ - r • (1 : ι → ℝ))) := by
  unfold quadForm
  -- s > 0
  have hs : 0 < ∑ i, tangencyDirection S μ r i :=
    (sum_tangencyDirection_pos_iff hS μ r).mpr hr
  have hsne : (∑ i, tangencyDirection S μ r i) ≠ 0 := ne_of_gt hs
  have he : (μ - r • (1 : ι → ℝ)) ≠ 0 :=
    excess_ne_zero_of_ne hS μ (ne_of_lt hr)
  have hq : 0 < (μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) :=
    pos_quad_of_posDef hS.inv he
  -- abbreviations
  set e : ι → ℝ := μ - r • (1 : ι → ℝ) with he_def
  set z : ι → ℝ := tangencyDirection S μ r with hz_def
  set s : ℝ := ∑ i, tangencyDirection S μ r i with hs_def
  have hz : z = S⁻¹ *ᵥ e := rfl
  have hwT : tangencyPortfolio S μ r = s⁻¹ • z := rfl
  have hsum : ∑ i, tangencyPortfolio S μ r i = 1 := sum_tangencyPortfolio S μ r hsne
  have hSz : S *ᵥ z = e := by rw [hz]; exact mulVec_inv_mulVec_cancel hS e
  -- numerator: μ ⬝ w_T - r = q / s
  have hnum : μ ⬝ᵥ (tangencyPortfolio S μ r) - r = ((e ⬝ᵥ (S⁻¹ *ᵥ e)) / s) := by
    have h1 : μ ⬝ᵥ (tangencyPortfolio S μ r) - r = e ⬝ᵥ (tangencyPortfolio S μ r) := by
      rw [he_def]
      exact excess_eq_of_sum_one μ (tangencyPortfolio S μ r) r hsum
    rw [h1, hwT, dotProduct_smul, smul_eq_mul]
    -- e ⬝ (s⁻¹ • z) = s⁻¹ * (e ⬝ z); e ⬝ z = e ⬝ (S⁻¹ e)
    have hez : e ⬝ᵥ z = e ⬝ᵥ (S⁻¹ *ᵥ e) := by rw [hz]
    rw [hez, div_eq_mul_inv, mul_comm]
  -- S w_T = s⁻¹ • e
  have hSwT : S *ᵥ (tangencyPortfolio S μ r) = s⁻¹ • e := by
    rw [hwT, Matrix.mulVec_smul, hSz]
  -- denominator quadratic: w_T ⬝ S w_T = q / s^2
  have hden : (tangencyPortfolio S μ r) ⬝ᵥ (S *ᵥ (tangencyPortfolio S μ r)) =
      (e ⬝ᵥ (S⁻¹ *ᵥ e)) / s ^ 2 := by
    rw [hwT, Matrix.mulVec_smul, hSz, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    have hze : z ⬝ᵥ e = e ⬝ᵥ (S⁻¹ *ᵥ e) := by
      rw [hz, dotProduct_comm]
    rw [hze]
    field_simp
  -- combine
  unfold sharpeRatio quadForm
  rw [hnum, hden]
  -- (q/s) / √(q/s²) = √q
  have hqnn : 0 ≤ e ⬝ᵥ (S⁻¹ *ᵥ e) := le_of_lt hq
  have hsnn : 0 ≤ s := le_of_lt hs
  have hsqrt : Real.sqrt ((e ⬝ᵥ (S⁻¹ *ᵥ e)) / s ^ 2) = Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) / s := by
    rw [Real.sqrt_div hqnn, Real.sqrt_sq hsnn]
  rw [hsqrt]
  -- (q/s)/(√q/s) = √q
  have hsqne : Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) ≠ 0 := by
    have : 0 < Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) := Real.sqrt_pos.mpr hq
    exact ne_of_gt this
  have hqeq : (e ⬝ᵥ (S⁻¹ *ᵥ e)) = Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) * Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) :=
    (Real.mul_self_sqrt hqnn).symm
  field_simp
  linarith [hqeq]

-- Symmetry helpers for CS
private theorem transpose_of_isHermitian_real {ι : Type*}
    {S : Matrix ι ι ℝ} (h : S.IsHermitian) : Sᵀ = S := by
  have h1 : Sᴴ = S := h.eq
  have h2 : Sᴴ = Sᵀ := conjTranspose_eq_transpose_of_trivial S
  rw [h2] at h1
  exact h1

private theorem dotProduct_mulVec_symm {ι : Type*} [Fintype ι]
    {S : Matrix ι ι ℝ} (h : S.IsHermitian) (x y : ι → ℝ) :
    x ⬝ᵥ (S *ᵥ y) = (S *ᵥ x) ⬝ᵥ y := by
  have hT : Sᵀ = S := transpose_of_isHermitian_real h
  rw [dotProduct_mulVec]
  have hvec : x ᵥ* S = S *ᵥ x := by
    have h1 : x ᵥ* Sᵀᵀ = Sᵀ *ᵥ x := vecMul_transpose Sᵀ x
    rw [transpose_transpose] at h1
    rw [hT] at h1
    exact h1
  rw [hvec]

private theorem csq_of_posDef {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (x y : ι → ℝ) :
    (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) := by
  have h := hA.star_dotProduct_mulVec_mul_le x y
  simpa [sq, pow_two] using h

-- Cauchy-Schwarz for Sharpe: (e⬝w)^2 ≤ q * (w⬝Sw)
private theorem csq_sharpe {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (e w : ι → ℝ) :
    ((e ⬝ᵥ w) ^ 2 ≤ ((e ⬝ᵥ (S⁻¹ *ᵥ e)) * (w ⬝ᵥ (S *ᵥ w)))) := by
  set z : ι → ℝ := S⁻¹ *ᵥ e with hz_def
  have hSz : S *ᵥ z = e := by
    rw [hz_def]; exact mulVec_inv_mulVec_cancel hS e
  have h1 : z ⬝ᵥ (S *ᵥ w) = e ⬝ᵥ w := by
    rw [dotProduct_mulVec_symm hS.isHermitian z w, hSz]
  have h2 : z ⬝ᵥ (S *ᵥ z) = e ⬝ᵥ (S⁻¹ *ᵥ e) := by
    rw [hSz]
    have hz2 : z = S⁻¹ *ᵥ e := rfl
    rw [hz2, dotProduct_comm]
  have hcs := csq_of_posDef hS z w
  rw [h1, h2] at hcs
  exact hcs

-- w ≠ 0 when fully invested
private theorem ne_zero_of_sum_one {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (hw : ∑ i, w i = 1) : w ≠ 0 := by
  intro hcon
  rw [hcon] at hw
  simp at hw

/-- **Tangency portfolio maximizes the Sharpe ratio.** If the risk-free return is below `μ_GMV`,
every fully invested portfolio has Sharpe ratio at most that of the tangency portfolio. -/
theorem sharpeRatio_le_sharpeRatio_tangencyPortfolio {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {S : Matrix ι ι ℝ} (hS : S.PosDef) (μ : ι → ℝ) {r : ℝ}
    (hr : r < ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ)) / ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1)))
    {w : ι → ℝ} (hw : ∑ i, w i = 1) :
    sharpeRatio S μ r w ≤ sharpeRatio S μ r (tangencyPortfolio S μ r) := by
  have he : (μ - r • (1 : ι → ℝ)) ≠ 0 :=
    excess_ne_zero_of_ne hS μ (ne_of_lt hr)
  have hq : 0 < (μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) :=
    pos_quad_of_posDef hS.inv he
  have hqnn : 0 ≤ (μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) := le_of_lt hq
  have hwne : w ≠ 0 := ne_zero_of_sum_one hw
  have hb : 0 < w ⬝ᵥ (S *ᵥ w) := pos_quad_of_posDef hS hwne
  have hsqrtb : 0 < Real.sqrt (w ⬝ᵥ (S *ᵥ w)) := Real.sqrt_pos.mpr hb
  -- rewrite Sharpe(w_T) to √q and Sharpe(w) numerator to e⬝w
  rw [sharpeRatio_tangencyPortfolio hS μ hr]
  set e : ι → ℝ := μ - r • (1 : ι → ℝ) with he_def
  have hexcess : μ ⬝ᵥ w - r = e ⬝ᵥ w := by
    rw [he_def]; exact excess_eq_of_sum_one μ w r hw
  unfold sharpeRatio quadForm
  rw [hexcess]
  -- goal: (e⬝w)/√(w⬝Sw) ≤ √q
  rw [div_le_iff₀ hsqrtb]
  -- goal: e⬝w ≤ √q * √(w⬝Sw)
  have hcs := csq_sharpe hS e w
  -- e⬝w ≤ √(q * (w⬝Sw)) = √q * √(w⬝Sw)
  have hsqrt_eq : Real.sqrt ((e ⬝ᵥ (S⁻¹ *ᵥ e)) * (w ⬝ᵥ (S *ᵥ w))) =
      Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) * Real.sqrt (w ⬝ᵥ (S *ᵥ w)) := by
    -- need 0 ≤ q for sqrt_mul
    have hqnn2 : 0 ≤ e ⬝ᵥ (S⁻¹ *ᵥ e) := by
      have : 0 ≤ (μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) := hqnn
      simpa [he_def] using this
    exact Real.sqrt_mul hqnn2 _
  have habs : e ⬝ᵥ w ≤ |(e ⬝ᵥ w)| := le_abs_self _
  have hsqrt_abs : Real.sqrt ((e ⬝ᵥ w) ^ 2) = |(e ⬝ᵥ w)| := Real.sqrt_sq_eq_abs _
  have hle : Real.sqrt ((e ⬝ᵥ w) ^ 2) ≤ Real.sqrt ((e ⬝ᵥ (S⁻¹ *ᵥ e)) * (w ⬝ᵥ (S *ᵥ w))) :=
    Real.sqrt_le_sqrt hcs
  rw [hsqrt_abs, hsqrt_eq] at hle
  -- hle : |e⬝w| ≤ √q * √b, so e⬝w ≤ √q * √b
  calc e ⬝ᵥ w ≤ |(e ⬝ᵥ w)| := habs
    _ ≤ Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) * Real.sqrt (w ⬝ᵥ (S *ᵥ w)) := hle
    _ = Real.sqrt ((μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ)))) *
        Real.sqrt (w ⬝ᵥ (S *ᵥ w)) := by rw [he_def]

-- s < 0 iff μ_GMV < r
private theorem sum_tangencyDirection_neg_iff {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (μ : ι → ℝ) (r : ℝ) :
    ∑ i, tangencyDirection S μ r i < 0 ↔
      ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ)) / ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1)) < r := by
  have h1ne : (1 : ι → ℝ) ≠ 0 := by
    intro hcon
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hi := congrFun hcon i
    simp at hi
  have hC : 0 < (1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1) := by
    have h := hS.inv.dotProduct_mulVec_pos h1ne
    simpa using h
  rw [sum_tangencyDirection, div_lt_iff₀ hC, sub_neg]

-- Sharpe(w_T) = -√q when s < 0
private theorem sharpeRatio_tangencyPortfolio_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (μ : ι → ℝ) {r : ℝ}
    (hr : ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ)) / ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1)) < r) :
    sharpeRatio S μ r (tangencyPortfolio S μ r) =
      -Real.sqrt ((μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ)))) := by
  have hs : ∑ i, tangencyDirection S μ r i < 0 :=
    (sum_tangencyDirection_neg_iff hS μ r).mpr hr
  have hsne : (∑ i, tangencyDirection S μ r i) ≠ 0 := ne_of_lt hs
  have he : (μ - r • (1 : ι → ℝ)) ≠ 0 :=
    excess_ne_zero_of_ne hS μ (ne_of_gt hr)
  have hq : 0 < (μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) :=
    pos_quad_of_posDef hS.inv he
  set e : ι → ℝ := μ - r • (1 : ι → ℝ) with he_def
  set z : ι → ℝ := tangencyDirection S μ r with hz_def
  set s : ℝ := ∑ i, tangencyDirection S μ r i with hs_def
  have hz : z = S⁻¹ *ᵥ e := rfl
  have hwT : tangencyPortfolio S μ r = s⁻¹ • z := rfl
  have hsum : ∑ i, tangencyPortfolio S μ r i = 1 := sum_tangencyPortfolio S μ r hsne
  have hSz : S *ᵥ z = e := by rw [hz]; exact mulVec_inv_mulVec_cancel hS e
  have hnum : μ ⬝ᵥ (tangencyPortfolio S μ r) - r = ((e ⬝ᵥ (S⁻¹ *ᵥ e)) / s) := by
    have h1 : μ ⬝ᵥ (tangencyPortfolio S μ r) - r = e ⬝ᵥ (tangencyPortfolio S μ r) := by
      rw [he_def]
      exact excess_eq_of_sum_one μ (tangencyPortfolio S μ r) r hsum
    rw [h1, hwT, dotProduct_smul, smul_eq_mul]
    have hez : e ⬝ᵥ z = e ⬝ᵥ (S⁻¹ *ᵥ e) := by rw [hz]
    rw [hez, div_eq_mul_inv, mul_comm]
  have hden : (tangencyPortfolio S μ r) ⬝ᵥ (S *ᵥ (tangencyPortfolio S μ r)) =
      (e ⬝ᵥ (S⁻¹ *ᵥ e)) / s ^ 2 := by
    rw [hwT, Matrix.mulVec_smul, hSz, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    have hze : z ⬝ᵥ e = e ⬝ᵥ (S⁻¹ *ᵥ e) := by
      rw [hz, dotProduct_comm]
    rw [hze]
    field_simp
  unfold sharpeRatio quadForm
  rw [hnum, hden]
  have hqnn : 0 ≤ e ⬝ᵥ (S⁻¹ *ᵥ e) := le_of_lt hq
  have habs : |s| = -s := abs_of_neg hs
  have hsqrt2 : Real.sqrt (s ^ 2) = -s := by
    rw [Real.sqrt_sq_eq_abs, habs]
  have hsqrt : Real.sqrt ((e ⬝ᵥ (S⁻¹ *ᵥ e)) / s ^ 2) = Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) / (-s) := by
    rw [Real.sqrt_div hqnn, hsqrt2]
  rw [hsqrt]
  have hsqne : Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) ≠ 0 := by
    have : 0 < Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) := Real.sqrt_pos.mpr hq
    exact ne_of_gt this
  have hqeq : (e ⬝ᵥ (S⁻¹ *ᵥ e)) = Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) * Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) :=
    (Real.mul_self_sqrt hqnn).symm
  -- (q/s)/(√q/(-s)) = -√q
  have hsne2 : -s ≠ 0 := by
    have : s < 0 := hs
    linarith
  field_simp
  linarith [hqeq]

/-- Negative-excess-return branch: if the risk-free return is above `μ_GMV`, the normalized
tangency portfolio minimizes the Sharpe ratio over fully invested portfolios. -/
theorem sharpeRatio_tangencyPortfolio_le_of_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {S : Matrix ι ι ℝ} (hS : S.PosDef) (μ : ι → ℝ) {r : ℝ}
    (hr : ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ μ)) / ((1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ 1)) < r)
    {w : ι → ℝ} (hw : ∑ i, w i = 1) :
    sharpeRatio S μ r (tangencyPortfolio S μ r) ≤ sharpeRatio S μ r w := by
  have he : (μ - r • (1 : ι → ℝ)) ≠ 0 :=
    excess_ne_zero_of_ne hS μ (ne_of_gt hr)
  have hq : 0 < (μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) :=
    pos_quad_of_posDef hS.inv he
  have hqnn : 0 ≤ (μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) := le_of_lt hq
  have hwne : w ≠ 0 := ne_zero_of_sum_one hw
  have hb : 0 < w ⬝ᵥ (S *ᵥ w) := pos_quad_of_posDef hS hwne
  have hsqrtb : 0 < Real.sqrt (w ⬝ᵥ (S *ᵥ w)) := Real.sqrt_pos.mpr hb
  rw [sharpeRatio_tangencyPortfolio_neg hS μ hr]
  set e : ι → ℝ := μ - r • (1 : ι → ℝ) with he_def
  have hexcess : μ ⬝ᵥ w - r = e ⬝ᵥ w := by
    rw [he_def]; exact excess_eq_of_sum_one μ w r hw
  unfold sharpeRatio quadForm
  rw [hexcess]
  -- goal: -√q ≤ (e⬝w)/√b
  rw [le_div_iff₀ hsqrtb]
  -- goal: -√q * √b ≤ e⬝w
  have hcs := csq_sharpe hS e w
  have hsqrt_eq : Real.sqrt ((e ⬝ᵥ (S⁻¹ *ᵥ e)) * (w ⬝ᵥ (S *ᵥ w))) =
      Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) * Real.sqrt (w ⬝ᵥ (S *ᵥ w)) := by
    have hqnn2 : 0 ≤ e ⬝ᵥ (S⁻¹ *ᵥ e) := by
      have : 0 ≤ (μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ))) := hqnn
      simpa [he_def] using this
    exact Real.sqrt_mul hqnn2 _
  have hsqrt_abs : Real.sqrt ((e ⬝ᵥ w) ^ 2) = |(e ⬝ᵥ w)| := Real.sqrt_sq_eq_abs _
  have hle : Real.sqrt ((e ⬝ᵥ w) ^ 2) ≤ Real.sqrt ((e ⬝ᵥ (S⁻¹ *ᵥ e)) * (w ⬝ᵥ (S *ᵥ w))) :=
    Real.sqrt_le_sqrt hcs
  rw [hsqrt_abs, hsqrt_eq] at hle
  -- hle : |e⬝w| ≤ √q * √b, so -√q*√b ≤ e⬝w
  have hneg : -(Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) * Real.sqrt (w ⬝ᵥ (S *ᵥ w))) ≤ e ⬝ᵥ w := by
    have h1 : -(Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) * Real.sqrt (w ⬝ᵥ (S *ᵥ w))) ≤ -|(e ⬝ᵥ w)| :=
      neg_le_neg hle
    have h2 : -|(e ⬝ᵥ w)| ≤ e ⬝ᵥ w := neg_abs_le _
    exact le_trans h1 h2
  have hconv : -Real.sqrt ((μ - r • (1 : ι → ℝ)) ⬝ᵥ (S⁻¹ *ᵥ (μ - r • (1 : ι → ℝ)))) *
      Real.sqrt (w ⬝ᵥ (S *ᵥ w)) =
      -(Real.sqrt (e ⬝ᵥ (S⁻¹ *ᵥ e)) * Real.sqrt (w ⬝ᵥ (S *ᵥ w))) := by
    rw [he_def, neg_mul]
  rw [hconv]
  exact hneg

end MathlibExt.Probability.Finance.TangencyPortfolio

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.TriangularIsingCriticalMomentum

open Filter Topology

namespace StatMech.FrontierA

noncomputable section

theorem hasDerivAt_real_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  convert h using 1
  · ext y
    simpa using Real.tanh_eq_sinh_div_cosh y
  · field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

@[fun_prop] theorem differentiable_real_tanh : Differentiable ℝ Real.tanh :=
  fun x => (hasDerivAt_real_tanh x).differentiableAt

def triangularIsingCriticalPolynomialAlong (J β : ℝ) : ℝ :=
  triangularIsingCriticalPolynomial (Real.tanh β) (Real.tanh (β * J))

def triangularIsingCriticalFactorAlong (J β : ℝ) : ℝ :=
  triangularIsingCriticalFactor β (β * J)

def triangularIsingZeroModePrefactorAlong (J β : ℝ) : ℝ :=
  Real.cosh β ^ 4 * Real.cosh (β * J) ^ 2

theorem differentiableAt_triangularIsingCriticalPolynomialAlong (J β : ℝ) :
    DifferentiableAt ℝ (triangularIsingCriticalPolynomialAlong J) β := by
  unfold triangularIsingCriticalPolynomialAlong triangularIsingCriticalPolynomial
  fun_prop

theorem differentiableAt_triangularIsingCriticalFactorAlong (J β : ℝ) :
    DifferentiableAt ℝ (triangularIsingCriticalFactorAlong J) β := by
  unfold triangularIsingCriticalFactorAlong triangularIsingCriticalFactor
  have hx : 1 - Real.tanh β ^ 2 ≠ 0 := by
    nlinarith [Real.neg_one_lt_tanh β, Real.tanh_lt_one β]
  have hy : 1 - Real.tanh (β * J) ^ 2 ≠ 0 := by
    nlinarith [Real.neg_one_lt_tanh (β * J), Real.tanh_lt_one (β * J)]
  apply DifferentiableAt.div
  · unfold triangularIsingCriticalCompanion
    fun_prop
  · fun_prop
  · exact mul_ne_zero (pow_ne_zero _ hx) hy

theorem continuous_triangularIsingZeroModePrefactorAlong (J : ℝ) :
    Continuous (triangularIsingZeroModePrefactorAlong J) := by
  unfold triangularIsingZeroModePrefactorAlong
  fun_prop



theorem deriv_triangularIsingCriticalPolynomialAlong_neg_at_root
    {β J : ℝ} (hβ : 0 < β) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate β (β * J) = 1) :
    deriv (triangularIsingCriticalPolynomialAlong J) β < 0 := by
  let P := triangularIsingCriticalPolynomialAlong J
  let Q := triangularIsingCriticalFactorAlong J
  have hPdiff := differentiableAt_triangularIsingCriticalPolynomialAlong J β
  have hQdiff := differentiableAt_triangularIsingCriticalFactorAlong J β
  have hP : HasDerivAt P (deriv P β) β := hPdiff.hasDerivAt
  have hQ : HasDerivAt Q (deriv Q β) β := hQdiff.hasDerivAt
  have hRate := (hasDerivAt_triangularIsingCriticalRateAlong β J).sub_const 1
  have hRateProd : HasDerivAt (fun b : ℝ => P b * Q b)
      (triangularIsingCriticalRateAlongDeriv β J) β := by
    convert hRate using 1
    ext b
    exact (triangularIsingCriticalRate_sub_one_eq_polynomial_mul_factor
      b (b * J)).symm
  have hProd := hP.mul hQ
  have hderivEq := hRateProd.unique hProd
  have hPzero : P β = 0 := by
    exact (triangularIsingCriticalPolynomial_zero_iff_rate_eq_one hβ).2 hroot
  have hQneg : Q β < 0 := triangularIsingCriticalFactor_neg hβ
  have hRatePos := triangularIsingCriticalRateAlongDeriv_pos_at_root hβ hJ hroot
  rw [hPzero, zero_mul, add_zero] at hderivEq
  have hprodPos : 0 < deriv P β * Q β := by linarith
  rcases mul_pos_iff.mp hprodPos with h | h
  · exact (lt_asymm hQneg h.2).elim
  · exact h.1

theorem triangularIsing_zeroMode_eq_polynomialAlong_sq_mul (J β : ℝ) :
    triangularIsingSymbol β β (β * J) 0 0 =
      triangularIsingCriticalPolynomialAlong J β ^ 2 *
        triangularIsingZeroModePrefactorAlong J β := by
  exact triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul β (β * J)



theorem triangularIsing_zeroMode_quadratic_tendsto_at_root
    {β J : ℝ} (hβ : 0 < β)
    (hroot : triangularIsingCriticalRate β (β * J) = 1) :
    Tendsto
      (fun t : ℝ =>
        triangularIsingSymbol (β + t) (β + t) ((β + t) * J) 0 0 / t ^ 2)
      (𝓝[≠] 0)
      (𝓝 (deriv (triangularIsingCriticalPolynomialAlong J) β ^ 2 *
        triangularIsingZeroModePrefactorAlong J β)) := by
  let P := triangularIsingCriticalPolynomialAlong J
  let H := triangularIsingZeroModePrefactorAlong J
  have hPdiff := differentiableAt_triangularIsingCriticalPolynomialAlong J β
  have hP : HasDerivAt P (deriv P β) β := hPdiff.hasDerivAt
  have hPzero : P β = 0 :=
    (triangularIsingCriticalPolynomial_zero_iff_rate_eq_one hβ).2 hroot
  have hslope := hP.tendsto_slope_zero
  have hid : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0) := tendsto_id
  have hargFull : Tendsto (fun t : ℝ => β + t) (𝓝 0) (𝓝 β) :=
    by simpa using tendsto_const_nhds.add hid
  have harg : Tendsto (fun t : ℝ => β + t) (𝓝[≠] 0) (𝓝 β) :=
    hargFull.mono_left inf_le_left
  have hHt : Tendsto (fun t : ℝ => H (β + t)) (𝓝[≠] 0) (𝓝 (H β)) :=
    (continuous_triangularIsingZeroModePrefactorAlong J).continuousAt.tendsto.comp harg
  have hmain := (hslope.pow 2).mul hHt
  change Tendsto _ _ (𝓝 (deriv P β ^ 2 * H β))
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  change (t⁻¹ • (P (β + t) - P β)) ^ 2 * H (β + t) =
    triangularIsingSymbol (β + t) (β + t) ((β + t) * J) 0 0 / t ^ 2
  rw [triangularIsing_zeroMode_eq_polynomialAlong_sq_mul, hPzero, sub_zero]
  simp only [smul_eq_mul]
  field_simp [ht0]
  rfl

theorem triangularIsing_zeroMode_quadratic_limit_pos
    {β J : ℝ} (hβ : 0 < β) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate β (β * J) = 1) :
    0 < deriv (triangularIsingCriticalPolynomialAlong J) β ^ 2 *
      triangularIsingZeroModePrefactorAlong J β := by
  have hd := deriv_triangularIsingCriticalPolynomialAlong_neg_at_root hβ hJ hroot
  have hdsq : 0 < deriv (triangularIsingCriticalPolynomialAlong J) β ^ 2 :=
    sq_pos_of_neg hd
  have hH : 0 < triangularIsingZeroModePrefactorAlong J β := by
    unfold triangularIsingZeroModePrefactorAlong
    positivity
  exact mul_pos hdsq hH

end

end StatMech.FrontierA

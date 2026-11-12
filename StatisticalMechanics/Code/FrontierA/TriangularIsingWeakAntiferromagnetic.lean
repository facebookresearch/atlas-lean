/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.TriangularIsingPhaseKernel

namespace StatMech.FrontierA

noncomputable section



theorem triangular_cosine_combination_le_zero_of_sum_nonneg
    {s r : Real} (hr : r < 0) (hsum : 0 <= s + 2 * r) (p q : Real) :
    s * (Real.cos p + Real.cos q) + r * Real.cos (p + q) <= 2 * s + r := by
  let A := (1 - Real.cos p) + (1 - Real.cos q)
  let B := 1 - Real.cos (p + q)
  have hA : 0 <= A := by
    dsimp [A]
    nlinarith [Real.cos_le_one p, Real.cos_le_one q]
  have hB : B <= 2 * A := by
    simpa only [A, B] using one_sub_cos_add_le_two_sum p q
  have hrB : 2 * r * A <= r * B := by
    have := mul_le_mul_of_nonpos_left hB hr.le
    nlinarith
  have hmain : 0 <= s * A + r * B := by
    have : 0 <= (s + 2 * r) * A := mul_nonneg hsum hA
    nlinarith
  dsimp [A, B] at hmain
  linarith



theorem triangular_hyperbolic_lower_pos_of_weak_neg_large
    {x y : Real} (hx : 0 < x) (hyUpper : y < 0)
    (hlarge : Real.sinh x < -2 * Real.sinh y) :
    0 < Real.cosh x ^ 2 * Real.cosh y +
        Real.sinh x ^ 2 * Real.sinh y +
        Real.sinh x ^ 2 / (2 * Real.sinh y) + Real.sinh y := by
  let s := Real.sinh x
  let r := Real.sinh y
  let cx := Real.cosh x
  let cy := Real.cosh y
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sinh_pos_iff.mpr hx
  have hr : r < 0 := by
    dsimp [r]
    exact Real.sinh_neg_iff.mpr hyUpper
  have hcy : 0 < cy := by dsimp [cy]; positivity
  have hcxSq : cx ^ 2 - s ^ 2 = 1 := by
    dsimp [cx, s]
    exact Real.cosh_sq_sub_sinh_sq x
  have hcySq : cy ^ 2 - r ^ 2 = 1 := by
    dsimp [cy, r]
    exact Real.cosh_sq_sub_sinh_sq y
  have hlarge' : s < -2 * r := by simpa only [s, r] using hlarge
  have hsumPos : 0 < s + (-2 * r) := by linarith
  have hsquare : s ^ 2 < (-2 * r) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hlarge') hsumPos]
  have hfactor : 0 < s ^ 2 + 1 := by positivity
  have hscaled : s ^ 2 * (s ^ 2 + 1) <
      4 * r ^ 2 * (s ^ 2 + 1) := by
    have hsquare' : s ^ 2 < 4 * r ^ 2 := by nlinarith [hsquare]
    exact mul_lt_mul_of_pos_right hsquare' hfactor
  have hsqCore : (s ^ 2 * cy) ^ 2 <
      ((-r) * (s ^ 2 + 2)) ^ 2 := by
    nlinarith [hcySq, hscaled]
  have hleft : 0 <= s ^ 2 * cy := mul_nonneg (sq_nonneg s) hcy.le
  have hright : 0 < (-r) * (s ^ 2 + 2) :=
    mul_pos (neg_pos.mpr hr) (by nlinarith [sq_nonneg s])
  have hcore : s ^ 2 * cy < (-r) * (s ^ 2 + 2) := by
    nlinarith
  have hcomparison :
      s ^ 2 * (cy - r) < (-2 * r) * (1 + s ^ 2) := by
    nlinarith
  have hcySqStrict : (-r) ^ 2 < cy ^ 2 := by
    nlinarith [hcySq]
  have hcyGt : -r < cy :=
    (sq_lt_sq₀ (neg_nonneg.mpr hr.le) hcy.le).mp hcySqStrict
  have hcyr : 0 < cy + r := by linarith
  have hunit : (cy - r) * (cy + r) = 1 := by
    nlinarith [hcySq]
  have hcomparison' :
      s ^ 2 < ((-2 * r) * (1 + s ^ 2)) * (cy + r) := by
    have hmul := mul_lt_mul_of_pos_right hcomparison hcyr
    calc
      s ^ 2 = (s ^ 2 * (cy - r)) * (cy + r) := by rw [mul_assoc, hunit, mul_one]
      _ < ((-2 * r) * (1 + s ^ 2)) * (cy + r) := hmul
  have hden : 0 < -2 * r := by linarith
  have hprod : 0 <
      (cx ^ 2 * cy + s ^ 2 * r + s ^ 2 / (2 * r) + r) * (-2 * r) := by
    have hr0 : r ≠ 0 := hr.ne
    have hcx : cx ^ 2 = 1 + s ^ 2 := by linarith [hcxSq]
    have hid :
        (cx ^ 2 * cy + s ^ 2 * r + s ^ 2 / (2 * r) + r) * (-2 * r) =
          ((-2 * r) * (1 + s ^ 2)) * (cy + r) - s ^ 2 := by
      rw [hcx]
      field_simp [hr0]
      ring
    rw [hid]
    linarith
  have hpositive : 0 < cx ^ 2 * cy + s ^ 2 * r + s ^ 2 / (2 * r) + r := by
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact (lt_asymm hden h.2).elim
  simpa only [cx, cy, s, r] using hpositive



theorem triangularIsingSymbol_pos_of_gt_neg_one_noncritical
    {beta J : Real} (hbeta : 0 < beta) (_hJ : -1 < J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (p q : Real) :
    0 < triangularIsingSymbol beta beta (beta * J) p q := by
  by_cases hJnonneg : 0 <= J
  · exact triangularIsingSymbol_pos_of_nonnegative_noncritical
      hbeta hJnonneg hcrit p q
  have hJneg : J < 0 := lt_of_not_ge hJnonneg
  let s := Real.sinh (2 * beta)
  let r := Real.sinh (2 * (beta * J))
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sinh_pos_iff.mpr (by linarith)
  have hr : r < 0 := by
    dsimp [r]
    have hbJ : beta * J < 0 := mul_neg_of_pos_of_neg hbeta hJneg
    exact Real.sinh_neg_iff.mpr (by linarith)
  by_cases hbranch : 0 <= s + 2 * r
  · have hzeroNe : triangularIsingSymbol beta beta (beta * J) 0 0 ≠ 0 := by
      intro hzero
      exact hcrit
        ((triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).1 hzero)
    have hzeroNonneg : 0 <= triangularIsingSymbol beta beta (beta * J) 0 0 := by
      rw [triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul]
      positivity
    have hzeroPos : 0 < triangularIsingSymbol beta beta (beta * J) 0 0 :=
      lt_of_le_of_ne hzeroNonneg (Ne.symm hzeroNe)
    have htrig := triangular_cosine_combination_le_zero_of_sum_nonneg
      hr hbranch p q
    unfold triangularIsingSymbol at hzeroPos ⊢
    simp only [Real.cos_zero, zero_add, mul_one] at hzeroPos
    change s * (Real.cos p + Real.cos q) + r * Real.cos (p + q) <=
      2 * s + r at htrig
    dsimp [s, r] at htrig
    nlinarith
  · have hlower := triangularIsingSymbol_equal_couplings_lower
      hbeta (mul_neg_of_pos_of_neg hbeta hJneg) p q
    have hyUpper : 2 * (beta * J) < 0 := by
      have hbJ : beta * J < 0 := mul_neg_of_pos_of_neg hbeta hJneg
      linarith
    have hlarge : Real.sinh (2 * beta) <
        -2 * Real.sinh (2 * (beta * J)) := by
      dsimp [s, r] at hbranch
      linarith
    have hpos := triangular_hyperbolic_lower_pos_of_weak_neg_large
      (x := 2 * beta) (y := 2 * (beta * J))
      (by positivity) hyUpper hlarge
    exact hpos.trans_le hlower



theorem triangularIsing_logSymbol_analyticAt_of_gt_neg_one_noncritical
    {beta J : Real} (hbeta : 0 < beta) (hJ : -1 < J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (p q : Real) :
    AnalyticAt Real
      (fun b : Real =>
        Real.log (triangularIsingSymbol b b (b * J) p q)) beta := by
  apply AnalyticAt.log (by unfold triangularIsingSymbol; fun_prop)
  exact triangularIsingSymbol_pos_of_gt_neg_one_noncritical
    hbeta hJ hcrit p q

end

end StatMech.FrontierA

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.TriangularIsingSymbol

namespace StatMech.FrontierA



theorem triangular_cosine_combination_le
    {a b : ℝ} (ha : 0 < a) (hb : b < 0) (p q : ℝ) :
    a * (Real.cos p + Real.cos q) + b * Real.cos (p + q) ≤
      -a ^ 2 / (2 * b) - b := by
  let u := (p + q) / 2
  let v := (p - q) / 2
  have hp : p = u + v := by dsimp [u, v]; ring
  have hq : q = u - v := by dsimp [u, v]; ring
  have hsum : Real.cos p + Real.cos q =
      2 * Real.cos u * Real.cos v := by
    rw [hp, hq, Real.cos_add, Real.cos_sub]
    ring
  have hpq : p + q = 2 * u := by dsimp [u]; ring
  have hdouble : Real.cos (p + q) = 2 * Real.cos u ^ 2 - 1 := by
    rw [hpq, Real.cos_two_mul]
  let r := |Real.cos u|
  have hr0 : 0 ≤ r := abs_nonneg _
  have hzw : Real.cos u * Real.cos v ≤ r := by
    calc
      Real.cos u * Real.cos v ≤ |Real.cos u * Real.cos v| := le_abs_self _
      _ = r * |Real.cos v| := by rw [abs_mul]
      _ ≤ r := mul_le_of_le_one_right hr0 (Real.abs_cos_le_one v)
  have hlinear :
      2 * a * (Real.cos u * Real.cos v) ≤ 2 * a * r := by
    gcongr
  have hrSq : r ^ 2 = Real.cos u ^ 2 := by
    dsimp [r]
    exact sq_abs (Real.cos u)
  have hden : 2 * b < 0 := by linarith
  have hfrac : 0 ≤ -(2 * b * r + a) ^ 2 / (2 * b) := by
    have hpos : 0 ≤ (2 * b * r + a) ^ 2 / (-2 * b) :=
      div_nonneg (sq_nonneg _) (by linarith)
    convert hpos using 1 <;> ring
  have hquad : 2 * a * r + b * (2 * r ^ 2 - 1) ≤
      -a ^ 2 / (2 * b) - b := by
    have hb0 : b ≠ 0 := hb.ne
    have hid :
        (-a ^ 2 / (2 * b) - b) -
            (2 * a * r + b * (2 * r ^ 2 - 1)) =
          -(2 * b * r + a) ^ 2 / (2 * b) := by
      field_simp [hb0]
      ring
    linarith
  rw [hsum, hdouble]
  calc
    a * (2 * Real.cos u * Real.cos v) +
          b * (2 * Real.cos u ^ 2 - 1) ≤
        2 * a * r + b * (2 * r ^ 2 - 1) := by
      rw [hrSq]
      linarith
    _ ≤ _ := hquad


theorem triangularIsingSymbol_equal_couplings_lower
    {x y : ℝ} (hx : 0 < x) (hy : y < 0) (p q : ℝ) :
    Real.cosh (2 * x) ^ 2 * Real.cosh (2 * y) +
          Real.sinh (2 * x) ^ 2 * Real.sinh (2 * y) +
          Real.sinh (2 * x) ^ 2 / (2 * Real.sinh (2 * y)) +
          Real.sinh (2 * y) ≤
      triangularIsingSymbol x x y p q := by
  have ha : 0 < Real.sinh (2 * x) := Real.sinh_pos_iff.mpr (by linarith)
  have hb : Real.sinh (2 * y) < 0 := Real.sinh_neg_iff.mpr (by linarith)
  have htrig := triangular_cosine_combination_le ha hb p q
  rw [triangularIsingSymbol]
  have hc : Real.cosh (2 * x) * Real.cosh (2 * x) = Real.cosh (2 * x) ^ 2 := by ring
  have hs : Real.sinh (2 * x) * Real.sinh (2 * x) = Real.sinh (2 * x) ^ 2 := by ring
  rw [hc, hs]
  calc
    Real.cosh (2 * x) ^ 2 * Real.cosh (2 * y) +
          Real.sinh (2 * x) ^ 2 * Real.sinh (2 * y) +
          Real.sinh (2 * x) ^ 2 / (2 * Real.sinh (2 * y)) +
          Real.sinh (2 * y) =
        (Real.cosh (2 * x) ^ 2 * Real.cosh (2 * y) +
          Real.sinh (2 * x) ^ 2 * Real.sinh (2 * y)) -
          (-Real.sinh (2 * x) ^ 2 / (2 * Real.sinh (2 * y)) -
            Real.sinh (2 * y)) := by ring
    _ ≤ (Real.cosh (2 * x) ^ 2 * Real.cosh (2 * y) +
          Real.sinh (2 * x) ^ 2 * Real.sinh (2 * y)) -
        (Real.sinh (2 * x) * (Real.cos p + Real.cos q) +
          Real.sinh (2 * y) * Real.cos (p + q)) :=
      sub_le_sub_left htrig _
    _ = _ := by ring

private theorem exp_mul_neg_two_sinh (y : ℝ) :
    Real.exp y * (-2 * Real.sinh y) = 1 - Real.exp (2 * y) := by
  rw [Real.sinh_eq]
  have hinv : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsq : Real.exp y * Real.exp y = Real.exp (2 * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

private theorem cosh_sq_mul_exp_neg_two_lt_one {x : ℝ} (hx : 0 < x) :
    Real.cosh x ^ 2 * Real.exp (-2 * x) < 1 := by
  let r := Real.exp (-2 * x)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hinv : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hnegSq : Real.exp (-x) ^ 2 = r := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hcosh : Real.cosh x * Real.exp (-x) = (1 + r) / 2 := by
    rw [Real.cosh_eq]
    calc
      (Real.exp x + Real.exp (-x)) / 2 * Real.exp (-x) =
          (Real.exp x * Real.exp (-x) + Real.exp (-x) ^ 2) / 2 := by ring
      _ = (1 + r) / 2 := by rw [hinv, hnegSq]
  have hz : 0 < (1 + r) / 2 ∧ (1 + r) / 2 < 1 := by
    constructor <;> linarith
  have hsq : (Real.cosh x * Real.exp (-x)) ^ 2 =
      Real.cosh x ^ 2 * r := by
    rw [mul_pow, hnegSq]
  rw [← hsq, hcosh]
  nlinarith [sq_nonneg ((1 + r) / 2)]



theorem triangular_hyperbolic_lower_pos
    {x y : ℝ} (hx : 0 < x) (hy : y ≤ -x) :
    0 < Real.cosh x ^ 2 * Real.cosh y +
        Real.sinh x ^ 2 * Real.sinh y +
        Real.sinh x ^ 2 / (2 * Real.sinh y) + Real.sinh y := by
  have hy0 : y < 0 := lt_of_le_of_lt hy (neg_lt_zero.mpr hx)
  have hb : Real.sinh y < 0 := Real.sinh_neg_iff.mpr hy0
  have hden : 0 < -2 * Real.sinh y := by linarith
  have hcs : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have hcb :
      Real.cosh x ^ 2 * Real.cosh y +
          Real.sinh x ^ 2 * Real.sinh y + Real.sinh y =
        Real.cosh x ^ 2 * Real.exp y := by
    rw [← Real.cosh_add_sinh y]
    nlinarith
  have hexpMono : Real.exp (2 * y) ≤ Real.exp (-2 * x) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hcoshExp := cosh_sq_mul_exp_neg_two_lt_one hx
  have hcore : Real.sinh x ^ 2 <
      Real.cosh x ^ 2 * (1 - Real.exp (2 * y)) := by
    have hc0 : 0 ≤ Real.cosh x ^ 2 := sq_nonneg _
    have hbound : Real.cosh x ^ 2 * Real.exp (2 * y) ≤
        Real.cosh x ^ 2 * Real.exp (-2 * x) := by gcongr
    nlinarith
  have hprod : 0 <
      (Real.cosh x ^ 2 * Real.exp y +
          Real.sinh x ^ 2 / (2 * Real.sinh y)) *
        (-2 * Real.sinh y) := by
    have hb0 : Real.sinh y ≠ 0 := hb.ne
    have hcancel : Real.sinh x ^ 2 / (2 * Real.sinh y) *
        (-2 * Real.sinh y) = -Real.sinh x ^ 2 := by field_simp [hb0]
    calc
      (Real.cosh x ^ 2 * Real.exp y +
          Real.sinh x ^ 2 / (2 * Real.sinh y)) *
          (-2 * Real.sinh y) =
        Real.cosh x ^ 2 * Real.exp y * (-2 * Real.sinh y) -
          Real.sinh x ^ 2 := by rw [add_mul, hcancel, sub_eq_add_neg]
      _ = Real.cosh x ^ 2 *
          (Real.exp y * (-2 * Real.sinh y)) - Real.sinh x ^ 2 := by ring
      _ = Real.cosh x ^ 2 * (1 - Real.exp (2 * y)) -
          Real.sinh x ^ 2 := by rw [exp_mul_neg_two_sinh]
      _ > 0 := by linarith
  have hsum : 0 < Real.cosh x ^ 2 * Real.exp y +
      Real.sinh x ^ 2 / (2 * Real.sinh y) := by
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact (lt_asymm hden h.2).elim
  calc
    0 < Real.cosh x ^ 2 * Real.exp y +
        Real.sinh x ^ 2 / (2 * Real.sinh y) := hsum
    _ = (Real.cosh x ^ 2 * Real.cosh y +
          Real.sinh x ^ 2 * Real.sinh y + Real.sinh y) +
        Real.sinh x ^ 2 / (2 * Real.sinh y) := by rw [hcb]
    _ = _ := by ring



theorem triangularIsingSymbol_pos_of_third_le_neg
    {x y : ℝ} (hx : 0 < x) (hy : y ≤ -x) (p q : ℝ) :
    0 < triangularIsingSymbol x x y p q := by
  have hy0 : y < 0 := lt_of_le_of_lt hy (neg_lt_zero.mpr hx)
  have hlower := triangularIsingSymbol_equal_couplings_lower hx hy0 p q
  have hpos := triangular_hyperbolic_lower_pos
    (x := 2 * x) (y := 2 * y) (by linarith) (by linarith)
  exact hpos.trans_le hlower

theorem continuous_log_triangularIsingSymbol_third_le_neg
    {x y : ℝ} (hx : 0 < x) (hy : y ≤ -x) :
    Continuous fun p : ℝ × ℝ =>
      Real.log (triangularIsingSymbol x x y p.1 p.2) :=
  continuous_log_triangularIsingSymbol_of_pos x x y
    (triangularIsingSymbol_pos_of_third_le_neg hx hy)

theorem triangularIsingSymbol_riemann_tendsto_symmetric_third_le_neg
    {x y : ℝ} (hx : 0 < x) (hy : y ≤ -x) :
    Filter.Tendsto
      (fun L : ℕ => (2 * Real.pi / L) ^ 2 *
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          Real.log (triangularIsingSymbol x x y
            (2 * Real.pi * i / L) (2 * Real.pi * j / L)))
      Filter.atTop
      (nhds (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol x x y k1 k2))) :=
  triangularIsingSymbol_riemann_tendsto_symmetric_of_pos x x y
    (triangularIsingSymbol_pos_of_third_le_neg hx hy)

end StatMech.FrontierA

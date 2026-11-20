/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.TriangularIsingWeakAntiferromagnetic

open Filter MeasureTheory Topology Complex

namespace StatMech.FrontierA

noncomputable section



def triangularIsingRaySymbolComplex
    (J : Real) (z : Complex) (p q : Real) : Complex :=
  Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) +
    Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
    (Complex.sinh (2 * z) * ((Real.cos p : Complex) + Real.cos q) +
      Complex.sinh (2 * z * J) * (Real.cos (p + q) : Complex))


def triangularIsingRaySymbolComplexDeriv
    (J : Real) (z : Complex) (p q : Real) : Complex :=
  4 * Complex.cosh (2 * z) * Complex.sinh (2 * z) *
      Complex.cosh (2 * z * J) +
    2 * J * Complex.cosh (2 * z) ^ 2 * Complex.sinh (2 * z * J) +
    4 * Complex.sinh (2 * z) * Complex.cosh (2 * z) *
      Complex.sinh (2 * z * J) +
    2 * J * Complex.sinh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
    2 * Complex.cosh (2 * z) * ((Real.cos p : Complex) + Real.cos q) -
    2 * J * Complex.cosh (2 * z * J) * (Real.cos (p + q) : Complex)

theorem triangularIsingRaySymbolComplex_ofReal
    (beta J p q : Real) :
    triangularIsingRaySymbolComplex J beta p q =
      (triangularIsingSymbol beta beta (beta * J) p q : Complex) := by
  have h2 : (2 : Complex) * beta = ((2 * beta : Real) : Complex) := by
    norm_num
  have hJ : ((2 * beta : Real) : Complex) * J =
      ((2 * (beta * J) : Real) : Complex) := by
    norm_num
    ring
  unfold triangularIsingRaySymbolComplex triangularIsingSymbol
  rw [h2, hJ, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  push_cast
  ring





def triangularIsingRayGap (beta J : Real) : Real :=
  if 0 <= J then
    triangularIsingSymbol beta beta (beta * J) 0 0
  else if 0 <= Real.sinh (2 * beta) +
      2 * Real.sinh (2 * (beta * J)) then
    triangularIsingSymbol beta beta (beta * J) 0 0
  else
    Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) +
      Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) +
      Real.sinh (2 * beta) ^ 2 /
        (2 * Real.sinh (2 * (beta * J))) +
      Real.sinh (2 * (beta * J))

theorem triangularIsingRayGap_pos
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    0 < triangularIsingRayGap beta J := by
  by_cases hJnonneg : 0 <= J
  · simp only [triangularIsingRayGap, if_pos hJnonneg]
    exact triangularIsingSymbol_pos_of_nonnegative_noncritical
      hbeta hJnonneg hcrit 0 0
  · have hJneg : J < 0 := lt_of_not_ge hJnonneg
    by_cases hbranch : 0 <= Real.sinh (2 * beta) +
        2 * Real.sinh (2 * (beta * J))
    · simp only [triangularIsingRayGap, if_neg hJnonneg, if_pos hbranch]
      have hzeroNe : triangularIsingSymbol beta beta (beta * J) 0 0 ≠ 0 := by
        intro hzero
        exact hcrit
          ((triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).1 hzero)
      have hzeroNonneg :
          0 <= triangularIsingSymbol beta beta (beta * J) 0 0 := by
        rw [triangularIsingSymbol_zero_eq_criticalPolynomial_sq_mul]
        positivity
      exact lt_of_le_of_ne hzeroNonneg (Ne.symm hzeroNe)
    · simp only [triangularIsingRayGap, if_neg hJnonneg, if_neg hbranch]
      apply triangular_hyperbolic_lower_pos_of_weak_neg_large
      · positivity
      · have hbJ : beta * J < 0 := mul_neg_of_pos_of_neg hbeta hJneg
        exact by linarith
      · linarith

theorem triangularIsingRayGap_le_symbol
    {beta J : Real} (hbeta : 0 < beta)
    (p q : Real) :
    triangularIsingRayGap beta J <=
      triangularIsingSymbol beta beta (beta * J) p q := by
  by_cases hJnonneg : 0 <= J
  · simp only [triangularIsingRayGap, if_pos hJnonneg]
    have hs : 0 <= Real.sinh (2 * beta) :=
      (Real.sinh_pos_iff.mpr (by linarith)).le
    have hr : 0 <= Real.sinh (2 * (beta * J)) :=
      Real.sinh_nonneg_iff.mpr (by positivity)
    have hA : 0 <= (1 - Real.cos p) + (1 - Real.cos q) := by
      nlinarith [Real.cos_le_one p, Real.cos_le_one q]
    have hB : 0 <= 1 - Real.cos (p + q) := by
      linarith [Real.cos_le_one (p + q)]
    have h := triangularIsingSymbol_sub_zero beta (beta * J) p q
    nlinarith [mul_nonneg hs hA, mul_nonneg hr hB]
  · have hJneg : J < 0 := lt_of_not_ge hJnonneg
    have hr : Real.sinh (2 * (beta * J)) < 0 := by
      apply Real.sinh_neg_iff.mpr
      have hbJ : beta * J < 0 := mul_neg_of_pos_of_neg hbeta hJneg
      linarith
    by_cases hbranch : 0 <= Real.sinh (2 * beta) +
        2 * Real.sinh (2 * (beta * J))
    · simp only [triangularIsingRayGap, if_neg hJnonneg, if_pos hbranch]
      have htrig := triangular_cosine_combination_le_zero_of_sum_nonneg
        hr hbranch p q
      unfold triangularIsingSymbol
      simp only [Real.cos_zero, zero_add, mul_one]
      nlinarith
    · simp only [triangularIsingRayGap, if_neg hJnonneg, if_neg hbranch]
      exact triangularIsingSymbol_equal_couplings_lower
        hbeta (mul_neg_of_pos_of_neg hbeta hJneg) p q



def triangularIsingComplexControl
    (beta J : Real) (z : Complex) : Real :=
  ‖Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
      (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)‖ +
  ‖Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
      (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)‖ +
  2 * ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)‖ +
  ‖Complex.sinh (2 * z * J) -
      (Real.sinh (2 * (beta * J)) : Complex)‖ +
  ‖Complex.cosh (2 * z) - (Real.cosh (2 * beta) : Complex)‖ +
  ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)‖ +
  ‖Complex.cosh (2 * z * J) -
      (Real.cosh (2 * (beta * J)) : Complex)‖ +
  ‖Complex.sinh (2 * z * J) -
      (Real.sinh (2 * (beta * J)) : Complex)‖

def triangularIsingComplexRadius (beta J : Real) : Real :=
  min (triangularIsingRayGap beta J / 2) 1

def triangularIsingComplexNeighborhood (beta J : Real) : Set Complex :=
  {z | triangularIsingComplexControl beta J z <
    triangularIsingComplexRadius beta J}

theorem continuous_triangularIsingComplexControl (beta J : Real) :
    Continuous (triangularIsingComplexControl beta J) := by
  unfold triangularIsingComplexControl
  fun_prop

theorem triangularIsingComplexControl_ofReal (beta J : Real) :
    triangularIsingComplexControl beta J beta = 0 := by
  have h2 : (2 : Complex) * beta = ((2 * beta : Real) : Complex) := by
    norm_num
  have hJ : ((2 * beta : Real) : Complex) * J =
      ((2 * (beta * J) : Real) : Complex) := by
    norm_num
    ring
  unfold triangularIsingComplexControl
  rw [h2, hJ, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  norm_num

theorem triangularIsingComplexRadius_pos
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    0 < triangularIsingComplexRadius beta J := by
  unfold triangularIsingComplexRadius
  exact lt_min (by positivity [triangularIsingRayGap_pos hbeta hcrit]) zero_lt_one

theorem triangularIsingComplexNeighborhood_isOpen (beta J : Real) :
    IsOpen (triangularIsingComplexNeighborhood beta J) := by
  exact isOpen_lt (continuous_triangularIsingComplexControl beta J) continuous_const

theorem triangularIsingComplexNeighborhood_mem_nhds
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    triangularIsingComplexNeighborhood beta J ∈ nhds (beta : Complex) := by
  apply (triangularIsingComplexNeighborhood_isOpen beta J).mem_nhds
  change triangularIsingComplexControl beta J beta <
    triangularIsingComplexRadius beta J
  rw [triangularIsingComplexControl_ofReal]
  exact triangularIsingComplexRadius_pos hbeta hcrit

theorem triangularIsingRaySymbolComplex_sub_ofReal_norm_le_control
    (beta J : Real) (z : Complex) (p q : Real) :
    ‖triangularIsingRaySymbolComplex J z p q -
        (triangularIsingSymbol beta beta (beta * J) p q : Complex)‖ <=
      triangularIsingComplexControl beta J z := by
  let A : Complex := (Real.cos p : Complex) + Real.cos q
  let B : Complex := (Real.cos (p + q) : Complex)
  have hA : ‖A‖ <= 2 := by
    calc
      ‖A‖ <= ‖(Real.cos p : Complex)‖ + ‖(Real.cos q : Complex)‖ :=
        norm_add_le _ _
      _ <= 2 := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        nlinarith [Real.abs_cos_le_one p, Real.abs_cos_le_one q]
  have hB : ‖B‖ <= 1 := by
    change ‖(Real.cos (p + q) : Complex)‖ <= 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one (p + q)
  rw [← triangularIsingRaySymbolComplex_ofReal beta J p q]
  have heq : triangularIsingRaySymbolComplex J z p q -
      triangularIsingRaySymbolComplex J beta p q =
      (Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
        (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)) +
      (Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
        (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)) -
      (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)) * A -
      (Complex.sinh (2 * z * J) -
        (Real.sinh (2 * (beta * J)) : Complex)) * B := by
    have h2 : (2 : Complex) * beta = ((2 * beta : Real) : Complex) := by
      norm_num
    have hJ' : ((2 * beta : Real) : Complex) * J =
        ((2 * (beta * J) : Real) : Complex) := by
      norm_num
      ring
    unfold triangularIsingRaySymbolComplex A B
    rw [h2, hJ', ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast
    ring
  rw [heq]
  calc
    _ <=
        ‖Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
          (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)‖ +
        ‖Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
          (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)‖ +
        ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)‖ * ‖A‖ +
        ‖Complex.sinh (2 * z * J) -
          (Real.sinh (2 * (beta * J)) : Complex)‖ * ‖B‖ := by
      let X := Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
        (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)
      let Y := Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
        (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)
      let U := (Complex.sinh (2 * z) -
        (Real.sinh (2 * beta) : Complex)) * A
      let V := (Complex.sinh (2 * z * J) -
        (Real.sinh (2 * (beta * J)) : Complex)) * B
      change ‖X + Y - U - V‖ <=
        ‖X‖ + ‖Y‖ + ‖Complex.sinh (2 * z) -
          (Real.sinh (2 * beta) : Complex)‖ * ‖A‖ +
        ‖Complex.sinh (2 * z * J) -
          (Real.sinh (2 * (beta * J)) : Complex)‖ * ‖B‖
      rw [← norm_mul, ← norm_mul]
      calc
        ‖X + Y - U - V‖ <= ‖X + Y - U‖ + ‖V‖ := norm_sub_le _ _
        _ <= (‖X + Y‖ + ‖U‖) + ‖V‖ := by
          nlinarith [norm_sub_le (X + Y) U]
        _ <= (‖X‖ + ‖Y‖ + ‖U‖) + ‖V‖ := by
          nlinarith [norm_add_le X Y]
    _ <= triangularIsingComplexControl beta J z := by
      have hn1 := norm_nonneg (Complex.sinh (2 * z) -
        (Real.sinh (2 * beta) : Complex))
      have hn2 := norm_nonneg (Complex.sinh (2 * z * J) -
        (Real.sinh (2 * (beta * J)) : Complex))
      unfold triangularIsingComplexControl
      nlinarith [mul_le_mul_of_nonneg_left hA hn1,
        mul_le_mul_of_nonneg_left hB hn2,
        norm_nonneg (Complex.cosh (2 * z) - (Real.cosh (2 * beta) : Complex)),
        norm_nonneg (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)),
        norm_nonneg (Complex.cosh (2 * z * J) -
          (Real.cosh (2 * (beta * J)) : Complex)),
        norm_nonneg (Complex.sinh (2 * z * J) -
          (Real.sinh (2 * (beta * J)) : Complex))]

theorem triangularIsingComplexRadius_le_gap_half (beta J : Real) :
    triangularIsingComplexRadius beta J <= triangularIsingRayGap beta J / 2 :=
  min_le_left _ _

theorem triangularIsingComplexRadius_le_one (beta J : Real) :
    triangularIsingComplexRadius beta J <= 1 := min_le_right _ _



theorem triangularIsingComplex_factor_bounds
    {beta J : Real} {z : Complex}
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    ‖Complex.cosh (2 * z)‖ < |Real.cosh (2 * beta)| + 1 ∧
    ‖Complex.sinh (2 * z)‖ < |Real.sinh (2 * beta)| + 1 ∧
    ‖Complex.cosh (2 * z * J)‖ < |Real.cosh (2 * (beta * J))| + 1 ∧
    ‖Complex.sinh (2 * z * J)‖ < |Real.sinh (2 * (beta * J))| + 1 := by
  let dP := ‖Complex.cosh (2 * z) ^ 2 * Complex.cosh (2 * z * J) -
    (Real.cosh (2 * beta) ^ 2 * Real.cosh (2 * (beta * J)) : Real)‖
  let dQ := ‖Complex.sinh (2 * z) ^ 2 * Complex.sinh (2 * z * J) -
    (Real.sinh (2 * beta) ^ 2 * Real.sinh (2 * (beta * J)) : Real)‖
  let dC := ‖Complex.cosh (2 * z) - (Real.cosh (2 * beta) : Complex)‖
  let dS := ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : Complex)‖
  let dCJ := ‖Complex.cosh (2 * z * J) -
    (Real.cosh (2 * (beta * J)) : Complex)‖
  let dSJ := ‖Complex.sinh (2 * z * J) -
    (Real.sinh (2 * (beta * J)) : Complex)‖
  have hsum : dP + dQ + 2 * dS + dSJ + dC + dS + dCJ + dSJ < 1 := by
    have hcontrol : triangularIsingComplexControl beta J z < 1 :=
      hz.trans_le (triangularIsingComplexRadius_le_one beta J)
    simpa [triangularIsingComplexControl, dP, dQ, dC, dS, dCJ, dSJ]
      using hcontrol
  have hdP0 : 0 <= dP := by dsimp [dP]; positivity
  have hdQ0 : 0 <= dQ := by dsimp [dQ]; positivity
  have hdC0 : 0 <= dC := by dsimp [dC]; positivity
  have hdS0 : 0 <= dS := by dsimp [dS]; positivity
  have hdCJ0 : 0 <= dCJ := by dsimp [dCJ]; positivity
  have hdSJ0 : 0 <= dSJ := by dsimp [dSJ]; positivity
  have hdC : dC < 1 := by
    nlinarith
  have hdS : dS < 1 := by
    nlinarith
  have hdCJ : dCJ < 1 := by
    nlinarith
  have hdSJ : dSJ < 1 := by
    nlinarith
  have bound_of_sub {w : Complex} {r : Real}
      (h : ‖w - (r : Complex)‖ < 1) : ‖w‖ < |r| + 1 := by
    calc
      ‖w‖ = ‖(w - (r : Complex)) + (r : Complex)‖ := by ring_nf
      _ <= ‖w - (r : Complex)‖ + ‖(r : Complex)‖ := norm_add_le _ _
      _ < |r| + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith
  exact ⟨bound_of_sub hdC, bound_of_sub hdS,
    bound_of_sub hdCJ, bound_of_sub hdSJ⟩

theorem triangularIsingRaySymbolComplex_re_pos
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    0 < (triangularIsingRaySymbolComplex J z p q).re := by
  let m := triangularIsingRayGap beta J
  let d := triangularIsingRaySymbolComplex J z p q -
    (triangularIsingSymbol beta beta (beta * J) p q : Complex)
  have hm : 0 < m := triangularIsingRayGap_pos hbeta hcrit
  have hd : ‖d‖ < m / 2 :=
    (triangularIsingRaySymbolComplex_sub_ofReal_norm_le_control beta J z p q).trans_lt
      (hz.trans_le (triangularIsingComplexRadius_le_gap_half beta J))
  have hdre : -‖d‖ <= d.re := neg_le_of_abs_le (Complex.abs_re_le_norm d)
  have hbase := triangularIsingRayGap_le_symbol (J := J) hbeta p q
  have hre : (triangularIsingRaySymbolComplex J z p q).re =
      triangularIsingSymbol beta beta (beta * J) p q + d.re := by
    dsimp [d]
    ring_nf
  rw [hre]
  dsimp [m] at hm hd hbase ⊢
  nlinarith

theorem triangularIsingRaySymbolComplex_mem_slitPlane
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    triangularIsingRaySymbolComplex J z p q ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (triangularIsingRaySymbolComplex_re_pos
    hbeta hcrit hz p q)

theorem triangularIsingRaySymbolComplex_norm_lower
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    triangularIsingRayGap beta J / 2 <
      ‖triangularIsingRaySymbolComplex J z p q‖ := by
  have hre := triangularIsingRaySymbolComplex_re_pos
    hbeta hcrit hz p q
  have hbase := triangularIsingRayGap_le_symbol (J := J) hbeta p q
  let d := triangularIsingRaySymbolComplex J z p q -
    (triangularIsingSymbol beta beta (beta * J) p q : Complex)
  have hd : ‖d‖ < triangularIsingRayGap beta J / 2 :=
    (triangularIsingRaySymbolComplex_sub_ofReal_norm_le_control beta J z p q).trans_lt
      (hz.trans_le (triangularIsingComplexRadius_le_gap_half beta J))
  have hdre : -‖d‖ <= d.re := neg_le_of_abs_le (Complex.abs_re_le_norm d)
  have hreEq : (triangularIsingRaySymbolComplex J z p q).re =
      triangularIsingSymbol beta beta (beta * J) p q + d.re := by
    dsimp [d]
    ring_nf
  have hrenorm := Complex.re_le_norm (triangularIsingRaySymbolComplex J z p q)
  rw [hreEq] at hrenorm
  nlinarith

def triangularIsingLogRaySymbolComplexDeriv
    (J : Real) (z : Complex) (p q : Real) : Complex :=
  triangularIsingRaySymbolComplexDeriv J z p q /
    triangularIsingRaySymbolComplex J z p q

def triangularIsingComplexDerivBound (beta J : Real) : Real :=
  let C := |Real.cosh (2 * beta)| + 1
  let S := |Real.sinh (2 * beta)| + 1
  let CJ := |Real.cosh (2 * (beta * J))| + 1
  let SJ := |Real.sinh (2 * (beta * J))| + 1
  4 * C * S * CJ + 2 * |J| * C ^ 2 * SJ +
    4 * S * C * SJ + 2 * |J| * S ^ 2 * CJ +
    4 * C + 2 * |J| * CJ

private theorem norm_add_four_sub_two_le
    (a b c d e f : Complex) :
    ‖a + b + c + d - e - f‖ <=
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  calc
    ‖a + b + c + d - e - f‖ <= ‖a + b + c + d - e‖ + ‖f‖ := norm_sub_le _ _
    _ <= (‖a + b + c + d‖ + ‖e‖) + ‖f‖ := by
      nlinarith [norm_sub_le (a + b + c + d) e]
    _ <= ((‖a + b + c‖ + ‖d‖) + ‖e‖) + ‖f‖ := by
      nlinarith [norm_add_le (a + b + c) d]
    _ <= (((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖ := by
      nlinarith [norm_add_le (a + b) c]
    _ <= ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
      nlinarith [norm_add_le a b]

theorem triangularIsingLogRaySymbolComplexDeriv_norm_le
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    ‖triangularIsingLogRaySymbolComplexDeriv J z p q‖ <=
      triangularIsingComplexDerivBound beta J /
        (triangularIsingRayGap beta J / 2) := by
  obtain ⟨hC, hS, hCJ, hSJ⟩ := triangularIsingComplex_factor_bounds hz
  have hA : ‖(Real.cos p : Complex) + Real.cos q‖ <= 2 := by
    calc
      _ <= ‖(Real.cos p : Complex)‖ + ‖(Real.cos q : Complex)‖ := norm_add_le _ _
      _ <= 2 := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
        nlinarith [Real.abs_cos_le_one p, Real.abs_cos_le_one q]
  have hB : ‖(Real.cos (p + q) : Complex)‖ <= 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  let C0 := |Real.cosh (2 * beta)| + 1
  let S0 := |Real.sinh (2 * beta)| + 1
  let CJ0 := |Real.cosh (2 * (beta * J))| + 1
  let SJ0 := |Real.sinh (2 * (beta * J))| + 1
  let t1 : Complex := 4 * Complex.cosh (2 * z) * Complex.sinh (2 * z) *
    Complex.cosh (2 * z * J)
  let t2 : Complex := 2 * J * Complex.cosh (2 * z) ^ 2 *
    Complex.sinh (2 * z * J)
  let t3 : Complex := 4 * Complex.sinh (2 * z) * Complex.cosh (2 * z) *
    Complex.sinh (2 * z * J)
  let t4 : Complex := 2 * J * Complex.sinh (2 * z) ^ 2 *
    Complex.cosh (2 * z * J)
  let t5 : Complex := 2 * Complex.cosh (2 * z) *
    ((Real.cos p : Complex) + Real.cos q)
  let t6 : Complex := 2 * J * Complex.cosh (2 * z * J) *
    (Real.cos (p + q) : Complex)
  have ht1 : ‖t1‖ <= 4 * C0 * S0 * CJ0 := by
    dsimp [t1, C0, S0, CJ0]
    simp only [norm_mul, norm_ofNat]
    gcongr
  have ht2 : ‖t2‖ <= 2 * |J| * C0 ^ 2 * SJ0 := by
    dsimp [t2, C0, SJ0]
    simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      norm_pow]
    gcongr
  have ht3 : ‖t3‖ <= 4 * S0 * C0 * SJ0 := by
    dsimp [t3, S0, C0, SJ0]
    simp only [norm_mul, norm_ofNat]
    gcongr
  have ht4 : ‖t4‖ <= 2 * |J| * S0 ^ 2 * CJ0 := by
    dsimp [t4, S0, CJ0]
    simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      norm_pow]
    gcongr
  have ht5 : ‖t5‖ <= 4 * C0 := by
    dsimp [t5, C0]
    simp only [norm_mul, norm_ofNat]
    have hnonneg : 0 <= ‖Complex.cosh (2 * z)‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hA hnonneg,
      mul_le_mul_of_nonneg_left hC.le (by norm_num : (0 : Real) <= 4)]
  have ht6 : ‖t6‖ <= 2 * |J| * CJ0 := by
    dsimp [t6, CJ0]
    simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    have hJ0 : 0 <= |J| := abs_nonneg J
    have hCJ0 : 0 <= ‖Complex.cosh (2 * z * J)‖ := norm_nonneg _
    have hfac : 0 <= 2 * |J| * ‖Complex.cosh (2 * z * J)‖ := by positivity
    calc
      2 * |J| * ‖Complex.cosh (2 * z * J)‖ *
          |Real.cos (p + q)| <=
          2 * |J| * ‖Complex.cosh (2 * z * J)‖ := by
        nth_rewrite 2 [← mul_one (2 * |J| * ‖Complex.cosh (2 * z * J)‖)]
        exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hfac
      _ <= 2 * |J| * (|Real.cosh (2 * (beta * J))| + 1) := by
        exact mul_le_mul_of_nonneg_left hCJ.le (by positivity)
  have hnum : ‖triangularIsingRaySymbolComplexDeriv J z p q‖ <=
      triangularIsingComplexDerivBound beta J := by
    calc
      ‖triangularIsingRaySymbolComplexDeriv J z p q‖ =
          ‖t1 + t2 + t3 + t4 - t5 - t6‖ := by rfl
      _ <= ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ + ‖t5‖ + ‖t6‖ :=
        norm_add_four_sub_two_le t1 t2 t3 t4 t5 t6
      _ <= 4 * C0 * S0 * CJ0 + 2 * |J| * C0 ^ 2 * SJ0 +
          4 * S0 * C0 * SJ0 + 2 * |J| * S0 ^ 2 * CJ0 +
          4 * C0 + 2 * |J| * CJ0 := by nlinarith
      _ = triangularIsingComplexDerivBound beta J := by
        simp [triangularIsingComplexDerivBound, C0, S0, CJ0, SJ0]
  have hden := triangularIsingRaySymbolComplex_norm_lower
    hbeta hcrit hz p q
  have hgap := triangularIsingRayGap_pos hbeta hcrit
  have hbound0 : 0 <= triangularIsingComplexDerivBound beta J := by
    unfold triangularIsingComplexDerivBound
    positivity
  rw [triangularIsingLogRaySymbolComplexDeriv, norm_div]
  exact div_le_div₀ hbound0 hnum (by positivity) hden.le

theorem hasDerivAt_triangularIsingRaySymbolComplex
    (J : Real) (z : Complex) (p q : Real) :
    HasDerivAt (fun w => triangularIsingRaySymbolComplex J w p q)
      (triangularIsingRaySymbolComplexDeriv J z p q) z := by
  have hlin : HasDerivAt (fun w : Complex => 2 * w) 2 z := by
    convert (hasDerivAt_id z).const_mul 2 using 1 <;> ring
  have hlinJ : HasDerivAt (fun w : Complex => 2 * w * J) (2 * J) z := by
    convert ((hasDerivAt_id z).const_mul 2).mul_const J using 1 <;> ring
  have hC := (Complex.hasDerivAt_cosh (2 * z)).comp z hlin
  have hS := (Complex.hasDerivAt_sinh (2 * z)).comp z hlin
  have hCJ := (Complex.hasDerivAt_cosh (2 * z * J)).comp z hlinJ
  have hSJ := (Complex.hasDerivAt_sinh (2 * z * J)).comp z hlinJ
  have h := ((hC.pow 2).mul hCJ).add ((hS.pow 2).mul hSJ) |>.sub
    ((hS.mul_const ((Real.cos p : Complex) + Real.cos q)).add
      (hSJ.mul_const (Real.cos (p + q) : Complex)))
  convert h using 1
  unfold triangularIsingRaySymbolComplexDeriv
  simp only [Function.comp_apply, Pi.pow_apply, Nat.reduceSub, pow_one]
  ring

theorem hasDerivAt_log_triangularIsingRaySymbolComplex
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) (p q : Real) :
    HasDerivAt (fun w => Complex.log (triangularIsingRaySymbolComplex J w p q))
      (triangularIsingLogRaySymbolComplexDeriv J z p q) z := by
  simpa [triangularIsingLogRaySymbolComplexDeriv] using
    (hasDerivAt_triangularIsingRaySymbolComplex J z p q).clog
      (triangularIsingRaySymbolComplex_mem_slitPlane hbeta hcrit hz p q)

theorem continuous_triangularIsingComplexLog_momenta
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    Continuous (fun x : Real × Real =>
      Complex.log (triangularIsingRaySymbolComplex J z x.1 x.2)) := by
  have hs : Continuous (fun x : Real × Real =>
      triangularIsingRaySymbolComplex J z x.1 x.2) := by
    unfold triangularIsingRaySymbolComplex
    fun_prop
  rw [continuous_iff_continuousAt]
  intro x
  have hlog : ContinuousAt Complex.log
      (triangularIsingRaySymbolComplex J z x.1 x.2) :=
    (Complex.hasDerivAt_log
      (triangularIsingRaySymbolComplex_mem_slitPlane
        hbeta hcrit hz x.1 x.2)).continuousAt
  exact ContinuousAt.comp'
    (f := fun y : Real × Real =>
      triangularIsingRaySymbolComplex J z y.1 y.2)
    hlog hs.continuousAt

theorem continuous_triangularIsingComplexLogDeriv_momenta
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    Continuous (fun x : Real × Real =>
      triangularIsingLogRaySymbolComplexDeriv J z x.1 x.2) := by
  unfold triangularIsingLogRaySymbolComplexDeriv
  apply Continuous.div
  · unfold triangularIsingRaySymbolComplexDeriv
    fun_prop
  · unfold triangularIsingRaySymbolComplex
    fun_prop
  · intro x hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.zero_re] at hre
    exact (triangularIsingRaySymbolComplex_re_pos
      hbeta hcrit hz x.1 x.2).ne' hre

theorem continuous_triangularIsingComplexInnerLog
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    Continuous (fun p => ∫ q in (-Real.pi)..Real.pi,
      Complex.log (triangularIsingRaySymbolComplex J z p q)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_triangularIsingComplexLog_momenta hbeta hcrit hz)
    (-Real.pi) Real.pi

theorem continuous_triangularIsingComplexInnerLogDeriv
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    Continuous (fun p => ∫ q in (-Real.pi)..Real.pi,
      triangularIsingLogRaySymbolComplexDeriv J z p q) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_triangularIsingComplexLogDeriv_momenta hbeta hcrit hz)
    (-Real.pi) Real.pi

theorem hasDerivAt_triangularIsingComplexInnerIntegral
    {beta J : Real} {z : Complex} (p : Real)
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    HasDerivAt (fun w => ∫ q in (-Real.pi)..Real.pi,
      Complex.log (triangularIsingRaySymbolComplex J w p q))
      (∫ q in (-Real.pi)..Real.pi,
        triangularIsingLogRaySymbolComplexDeriv J z p q) z := by
  let C := triangularIsingComplexDerivBound beta J /
    (triangularIsingRayGap beta J / 2)
  have hs : triangularIsingComplexNeighborhood beta J ∈ nhds z :=
    (triangularIsingComplexNeighborhood_isOpen beta J).mem_nhds hz
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w q => Complex.log (triangularIsingRaySymbolComplex J w p q))
    (F' := fun w q => triangularIsingLogRaySymbolComplexDeriv J w p q)
    (bound := fun _ => C) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with w hw
    exact ((continuous_triangularIsingComplexLog_momenta
      hbeta hcrit hw).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ((continuous_triangularIsingComplexLog_momenta
      hbeta hcrit hz).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact ((continuous_triangularIsingComplexLogDeriv_momenta
      hbeta hcrit hz).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with q _hq w hw
    simpa only [C] using
      triangularIsingLogRaySymbolComplexDeriv_norm_le
        hbeta hcrit hw p q
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with q _hq w hw
    exact hasDerivAt_log_triangularIsingRaySymbolComplex
      hbeta hcrit hw p q

theorem hasDerivAt_triangularIsingComplexDoubleIntegral
    {beta J : Real} {z : Complex}
    (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hz : z ∈ triangularIsingComplexNeighborhood beta J) :
    HasDerivAt (fun w => ∫ p in (-Real.pi)..Real.pi,
      ∫ q in (-Real.pi)..Real.pi,
        Complex.log (triangularIsingRaySymbolComplex J w p q))
      (∫ p in (-Real.pi)..Real.pi,
        ∫ q in (-Real.pi)..Real.pi,
          triangularIsingLogRaySymbolComplexDeriv J z p q) z := by
  let C := triangularIsingComplexDerivBound beta J /
    (triangularIsingRayGap beta J / 2)
  let B := C * (2 * Real.pi)
  have hs : triangularIsingComplexNeighborhood beta J ∈ nhds z :=
    (triangularIsingComplexNeighborhood_isOpen beta J).mem_nhds hz
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w p => ∫ q in (-Real.pi)..Real.pi,
      Complex.log (triangularIsingRaySymbolComplex J w p q))
    (F' := fun w p => ∫ q in (-Real.pi)..Real.pi,
      triangularIsingLogRaySymbolComplexDeriv J w p q)
    (bound := fun _ => B) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with w hw
    exact (continuous_triangularIsingComplexInnerLog
      hbeta hcrit hw).aestronglyMeasurable
  · exact (continuous_triangularIsingComplexInnerLog
      hbeta hcrit hz).intervalIntegrable _ _
  · exact (continuous_triangularIsingComplexInnerLogDeriv
      hbeta hcrit hz).aestronglyMeasurable
  · filter_upwards [] with p _hp w hw
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi) (b := Real.pi)
      (f := fun q => triangularIsingLogRaySymbolComplexDeriv J w p q)
      (C := C) (fun q _hq => by
        simpa only [C] using
          triangularIsingLogRaySymbolComplexDeriv_norm_le
            hbeta hcrit hw p q)
    calc
      ‖∫ q in (-Real.pi)..Real.pi,
          triangularIsingLogRaySymbolComplexDeriv J w p q‖ <=
          C * |Real.pi - (-Real.pi)| := hbound
      _ = B := by
        rw [abs_of_pos (by linarith [Real.pi_pos])]
        simp only [B]
        ring
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with p _hp w hw
    exact hasDerivAt_triangularIsingComplexInnerIntegral
      p hbeta hcrit hw



def triangularIsingFreeEnergyRayComplex (J : Real) (z : Complex) : Complex :=
  -(Real.log 2 : Complex) - (1 / (8 * Real.pi ^ 2) : Complex) *
    ∫ p in (-Real.pi)..Real.pi,
      ∫ q in (-Real.pi)..Real.pi,
        Complex.log (triangularIsingRaySymbolComplex J z p q)

theorem differentiableOn_triangularIsingFreeEnergyRayComplex
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    DifferentiableOn Complex (triangularIsingFreeEnergyRayComplex J)
      (triangularIsingComplexNeighborhood beta J) := by
  intro z hz
  unfold triangularIsingFreeEnergyRayComplex
  exact ((hasDerivAt_const z (-(Real.log 2 : Complex))).sub
    ((hasDerivAt_triangularIsingComplexDoubleIntegral
      hbeta hcrit hz).const_mul
        (1 / (8 * Real.pi ^ 2) : Complex))).differentiableAt.differentiableWithinAt

theorem analyticAt_triangularIsingFreeEnergyRayComplex
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    AnalyticAt Complex (triangularIsingFreeEnergyRayComplex J) beta := by
  exact (differentiableOn_triangularIsingFreeEnergyRayComplex
    hbeta hcrit).analyticAt
      (triangularIsingComplexNeighborhood_mem_nhds hbeta hcrit)

theorem triangularIsingComplexLog_ofReal
    {beta J b : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hb : (b : Complex) ∈ triangularIsingComplexNeighborhood beta J)
    (p q : Real) :
    Complex.log (triangularIsingRaySymbolComplex J b p q) =
      (Real.log (triangularIsingSymbol b b (b * J) p q) : Complex) := by
  rw [triangularIsingRaySymbolComplex_ofReal]
  have hpos : 0 < triangularIsingSymbol b b (b * J) p q := by
    have := triangularIsingRaySymbolComplex_re_pos
      hbeta hcrit hb p q
    simpa [triangularIsingRaySymbolComplex_ofReal] using this
  exact (Complex.ofReal_log hpos.le).symm

theorem triangularIsingComplexDoubleIntegral_ofReal
    {beta J b : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hb : (b : Complex) ∈ triangularIsingComplexNeighborhood beta J) :
    (∫ p in (-Real.pi)..Real.pi,
      ∫ q in (-Real.pi)..Real.pi,
        Complex.log (triangularIsingRaySymbolComplex J b p q)) =
      Complex.ofReal (∫ p in (-Real.pi)..Real.pi,
        ∫ q in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol b b (b * J) p q)) := by
  calc
    _ = ∫ p in (-Real.pi)..Real.pi,
        Complex.ofReal (∫ q in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol b b (b * J) p q)) := by
      apply intervalIntegral.integral_congr
      intro p _hp
      calc
        _ = ∫ q in (-Real.pi)..Real.pi,
            (Real.log (triangularIsingSymbol b b (b * J) p q) : Complex) := by
          apply intervalIntegral.integral_congr
          intro q _hq
          exact triangularIsingComplexLog_ofReal hbeta hcrit hb p q
        _ = _ := intervalIntegral.integral_ofReal
    _ = _ := intervalIntegral.integral_ofReal

theorem triangularIsingFreeEnergyRayComplex_ofReal
    {beta J b : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hb : (b : Complex) ∈ triangularIsingComplexNeighborhood beta J) :
    triangularIsingFreeEnergyRayComplex J b =
      (triangularIsingFreeEnergyValue b b (b * J) : Complex) := by
  unfold triangularIsingFreeEnergyRayComplex triangularIsingFreeEnergyValue
  rw [triangularIsingComplexDoubleIntegral_ofReal hbeta hcrit hb]
  push_cast
  ring





theorem triangularIsingFreeEnergyValue_analyticAt_of_noncritical
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    AnalyticAt Real
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
  have hc := (analyticAt_triangularIsingFreeEnergyRayComplex
    hbeta hcrit).re_ofReal
  apply hc.congr
  have hev : ∀ᶠ b : Real in nhds beta,
      (b : Complex) ∈ triangularIsingComplexNeighborhood beta J :=
    (Complex.continuous_ofReal.tendsto beta)
      (triangularIsingComplexNeighborhood_mem_nhds hbeta hcrit)
  filter_upwards [hev] with b hb
  rw [triangularIsingFreeEnergyRayComplex_ofReal hbeta hcrit hb]
  simp



theorem triangularIsingFreeEnergyValue_analyticAt_of_gt_neg_one_noncritical
    {beta J : Real} (hbeta : 0 < beta) (_hJ : -1 < J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    AnalyticAt Real
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
  triangularIsingFreeEnergyValue_analyticAt_of_noncritical hbeta hcrit




theorem triangularIsingCriticalRate_ne_one_of_le_neg_one
    {beta J : Real} (hbeta : 0 < beta) (hJ : J <= -1) :
    triangularIsingCriticalRate beta (beta * J) ≠ 1 := by
  intro hcrit
  have hzero : triangularIsingSymbol beta beta (beta * J) 0 0 = 0 :=
    (triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).2 hcrit
  have hthird : beta * J <= -beta := by
    nlinarith
  exact (triangularIsingSymbol_pos_of_third_le_neg hbeta hthird 0 0).ne' hzero



theorem triangularIsingFreeEnergyValue_analyticAt_of_le_neg_one
    {beta J : Real} (hbeta : 0 < beta) (hJ : J <= -1) :
    AnalyticAt Real
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
  triangularIsingFreeEnergyValue_analyticAt_of_noncritical hbeta
    (triangularIsingCriticalRate_ne_one_of_le_neg_one hbeta hJ)

theorem triangularIsingFreeEnergyValue_analyticAt_of_nonnegative_noncritical
    {beta J : Real} (hbeta : 0 < beta) (_hJ : 0 <= J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    AnalyticAt Real
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
  triangularIsingFreeEnergyValue_analyticAt_of_noncritical hbeta hcrit

end

end StatMech.FrontierA

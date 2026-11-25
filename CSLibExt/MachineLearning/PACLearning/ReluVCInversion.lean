/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.GrowthFunction
public import CSLibExt.MachineLearning.PACLearning.TraceCard
public import Cslib.MachineLearning.PACLearning.VCDimension
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# VC inversion of the BHLM shatter bound

The numeric last step of the piecewise-linear (ReLU) network VC
bound of Bartlett, Harvey, Liaw and Mehrabian, as presented in
Telgarsky's deep learning theory notes (Theorem 17.4): if a
Boolean class has growth function at most `(12 n L) ^ (p L)`
(with `pL² ≥ 72` and `p ≥ 2`), then its VC dimension is at most
`6 pL ln (pL)`. The hypothesis `2 ≤ p` is needed: at `(p, L) =
(1, 9)` the bare inversion fails.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

/-- Coarse lower bound on `log 2`. -/
private theorem log_two_ge : (2 / 3 : ℝ) ≤ Real.log 2 :=
  (lt_trans (show (2 / 3 : ℝ) < 0.6931471803 by norm_num)
    Real.log_two_gt_d9).le

/-- Coarse upper bound on `log 2`. -/
private theorem log_two_le : Real.log 2 ≤ (7 / 10 : ℝ) :=
  (lt_trans Real.log_two_lt_d9
    (show (0.6931471808 : ℝ) < 7 / 10 by norm_num)).le

/-- Coarse lower bound on `log 3`. -/
private theorem log_three_ge : (1 : ℝ) ≤ Real.log 3 :=
  (lt_trans (show (1 : ℝ) < 1.0986122885 by norm_num)
    Real.log_three_gt_d9).le

/-- Coarse upper bound on `log 3`. -/
private theorem log_three_le : Real.log 3 ≤ (11 / 10 : ℝ) :=
  (lt_trans Real.log_three_lt_d9
    (show (1.0986122888 : ℝ) < 11 / 10 by norm_num)).le

/-- `log 72 = 3 log 2 + 2 log 3`. -/
private theorem log_seventy_two :
    Real.log 72 = 3 * Real.log 2 + 2 * Real.log 3 := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [show (72 : ℝ) = 8 * 9 by norm_num,
    Real.log_mul (show (8 : ℝ) ≠ 0 by norm_num)
      (show (9 : ℝ) ≠ 0 by norm_num), h8, h9]

/-- `log 12 = 2 log 2 + log 3`. -/
private theorem log_twelve :
    Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
  rw [show (12 : ℝ) = 4 * 3 by norm_num,
    Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num)
      (show (3 : ℝ) ≠ 0 by norm_num), Real.log_four_eq]

/-- From `72 ≤ p * L ^ 2`, the depth is positive. -/
private theorem bhlm_L_ge_one (p L : ℕ) (hpL : 72 ≤ p * L ^ 2) :
    1 ≤ L := by
  rcases Nat.eq_zero_or_pos L with rfl | hpos
  · simp at hpL
  · exact hpos

/-- From `2 ≤ p` and `72 ≤ p * L ^ 2`, `12 ≤ p * L`. -/
private theorem bhlm_pL_ge_twelve (p L : ℕ) (hp : 2 ≤ p)
    (hpL : 72 ≤ p * L ^ 2) : 12 ≤ p * L := by
  have hsq : (p * L) ^ 2 = p * (p * L ^ 2) := by ring
  have h144 : (144 : ℕ) ≤ p * (p * L ^ 2) := by
    calc (144 : ℕ) = 2 * 72 := by norm_num
      _ ≤ p * (p * L ^ 2) := Nat.mul_le_mul hp hpL
  have hge : (144 : ℕ) ≤ (p * L) ^ 2 := by
    rw [hsq]
    exact h144
  by_contra hc
  rw [not_le] at hc
  have hlt : (p * L) ^ 2 < 12 ^ 2 := Nat.pow_lt_pow_left hc (by norm_num)
  norm_num at hlt
  omega

/-- Strict increase of `x ↦ x * L2 - A * log x` on points above `A / L2`. -/
private theorem slope_strict_mono (A L2 x x' : ℝ) (hA1 : 1 ≤ A)
    (hL2 : 0 < L2) (hdiv : A / L2 ≤ x) (hlt : x < x') (hxpos : 0 < x) :
    x * L2 - A * Real.log x < x' * L2 - A * Real.log x' := by
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hx'pos : (0 : ℝ) < x' := lt_trans hxpos hlt
  have hstrict : Real.log (x' / x) < (x' - x) / x := by
    have hgt : (1 : ℝ) < x' / x := by
      rw [lt_div_iff₀ hxpos]
      simpa using hlt
    have hne : x' / x ≠ 1 := ne_of_gt hgt
    have hle := Real.log_lt_sub_one_of_pos (div_pos hx'pos hxpos) hne
    have heq : (x' - x) / x = x' / x - 1 := by
      rw [sub_div, div_self hxpos.ne']
    rw [heq]
    exact hle
  have hAmul : A * Real.log (x' / x) < A * ((x' - x) / x) :=
    mul_lt_mul_of_pos_left hstrict hApos
  have hAx : A / x ≤ L2 := by
    have h2 : A ≤ x * L2 := by
      have hdiv' := hdiv
      rwa [div_le_iff₀ hL2] at hdiv'
    rwa [div_le_iff₀ hxpos, mul_comm L2 x]
  have hfin : A * ((x' - x) / x) ≤ (x' - x) * L2 := by
    have hnn : (0 : ℝ) ≤ x' - x := sub_nonneg.mpr hlt.le
    calc A * ((x' - x) / x) = (x' - x) * (A / x) := by ring
      _ ≤ (x' - x) * L2 := mul_le_mul_of_nonneg_left hAx hnn
  have hchain : A * Real.log (x' / x) < (x' - x) * L2 :=
    lt_of_lt_of_le hAmul hfin
  have hlogeq : Real.log (x' / x) = Real.log x' - Real.log x :=
    Real.log_div hx'pos.ne' hxpos.ne'
  have hpos : (0 : ℝ) < (x' - x) * L2 - A * (Real.log x' - Real.log x) := by
    rw [← hlogeq]
    exact sub_pos.mpr hchain
  have hdecomp : (x' - x) * L2 - A * (Real.log x' - Real.log x) =
      (x' * L2 - A * Real.log x') - (x * L2 - A * Real.log x) := by
    ring
  rw [hdecomp] at hpos
  exact sub_pos.mp hpos

/-- Core estimate at the threshold point: for `lp`, `ll` with
`log 2 ≤ lp`, `0 ≤ ll`, `4 ≤ lp + 2 * ll` and `0 < lp + ll`,
`log 72 ≤ (6 * log 2 - 1) * lp + (6 * log 2 - 2) * ll - log (lp + ll)`. -/
private theorem base_inequality (lp ll : ℝ) (hlp : Real.log 2 ≤ lp)
    (hll : (0 : ℝ) ≤ ll) (hsum : (4 : ℝ) ≤ lp + 2 * ll)
    (hy : (0 : ℝ) < lp + ll) :
    Real.log 72 ≤ (6 * Real.log 2 - 1) * lp + (6 * Real.log 2 - 2) * ll -
      Real.log (lp + ll) := by
  have htan : Real.log (lp + ll) ≤ (lp + ll) / 2 + (Real.log 2 - 1) := by
    have hpos2 : (0 : ℝ) < (lp + ll) / 2 := by linarith only [hy]
    have h := Real.log_le_sub_one_of_pos hpos2
    rw [Real.log_div (ne_of_gt hy) (show (2 : ℝ) ≠ 0 by norm_num)] at h
    linarith only [h]
  have hc1 : (5 / 2 : ℝ) ≤ 6 * Real.log 2 - 3 / 2 := by
    have h := log_two_ge
    linarith only [h]
  have hc2 : (3 / 2 : ℝ) ≤ 6 * Real.log 2 - 5 / 2 := by
    have h := log_two_ge
    linarith only [h]
  have hconst : (3 / 10 : ℝ) ≤ 1 - Real.log 2 := by
    have h := log_two_le
    linarith only [h]
  have h72lo : (4 : ℝ) ≤ Real.log 72 := by
    rw [log_seventy_two]
    linarith only [log_two_ge, log_three_ge]
  have h72hi : Real.log 72 ≤ (43 / 10 : ℝ) := by
    rw [log_seventy_two]
    linarith only [log_two_le, log_three_le]
  have hlp2 : (2 / 3 : ℝ) ≤ lp := le_trans log_two_ge hlp
  have hlp_nn : (0 : ℝ) ≤ lp := le_trans (by norm_num) hlp2
  have hmain : (67 / 15 : ℝ) ≤ (5 / 2) * lp + (3 / 2) * ll + 3 / 10 := by
    have hdecomp : (5 / 2 : ℝ) * lp + (3 / 2) * ll =
        (7 / 4) * lp + (3 / 4) * (lp + 2 * ll) := by ring
    rw [hdecomp]
    have g1 : (7 / 4 : ℝ) * (2 / 3) ≤ (7 / 4) * lp :=
      mul_le_mul_of_nonneg_left hlp2 (show (0 : ℝ) ≤ 7 / 4 by norm_num)
    have g2 : (3 / 4 : ℝ) * 4 ≤ (3 / 4) * (lp + 2 * ll) :=
      mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 3 / 4 by norm_num)
    have hnum : (67 / 15 : ℝ) = (7 / 4) * (2 / 3) + (3 / 4) * 4 + 3 / 10 := by
      norm_num
    rw [hnum]
    linarith only [g1, g2]
  have e1 : (5 / 2 : ℝ) * lp ≤ (6 * Real.log 2 - 3 / 2) * lp :=
    mul_le_mul_of_nonneg_right hc1 hlp_nn
  have e2 : (3 / 2 : ℝ) * ll ≤ (6 * Real.log 2 - 5 / 2) * ll :=
    mul_le_mul_of_nonneg_right hc2 hll
  have hF : (5 / 2 : ℝ) * lp + (3 / 2) * ll + 3 / 10 ≤
      (6 * Real.log 2 - 1) * lp + (6 * Real.log 2 - 2) * ll -
        Real.log (lp + ll) := by
    linarith only [e1, e2, hconst, htan]
  have hfin : (43 / 10 : ℝ) ≤ 67 / 15 := by norm_num
  linarith only [h72hi, hmain, hF, hfin]

/-- Inversion of the BHLM shatter bound: if
`2 ^ n ≤ (12 n L) ^ (p L)` with `2 ≤ p` and `72 ≤ p L²`, then
`n ≤ 6 pL log (pL)`. -/
theorem le_six_mul_log_of_two_pow_le_bhlm (p L n : ℕ) (hp : 2 ≤ p)
    (hpL : 72 ≤ p * L ^ 2)
    (h : (2 : ℝ) ^ n ≤ (12 * (n : ℝ) * (L : ℝ)) ^ (p * L)) :
    (n : ℝ) ≤ 6 * ((p * L : ℕ) : ℝ) * Real.log ((p * L : ℕ) : ℝ) := by
  set A : ℝ := ((p * L : ℕ) : ℝ) with hAdef
  have hbase : (12 : ℝ) * (n : ℝ) * (L : ℝ) = 12 * (L : ℝ) * (n : ℝ) := by
    ring
  rw [hbase] at h
  have hL1 : 1 ≤ L := bhlm_L_ge_one p L hpL
  have hp0 : p ≠ 0 := by omega
  have hL0 : L ≠ 0 := by omega
  have h12 : 12 ≤ p * L := bhlm_pL_ge_twelve p L hp hpL
  have hA12 : (12 : ℝ) ≤ A := by
    rw [hAdef]
    exact_mod_cast h12
  have hA1 : (1 : ℝ) ≤ A := by linarith only [hA12]
  have hApos : (0 : ℝ) < A := by linarith only [hA12]
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hAeq : A = (p : ℝ) * (L : ℝ) := by
    rw [hAdef, Nat.cast_mul]
  have hlogA_eq : Real.log A = Real.log p + Real.log L := by
    rw [hAeq, Real.log_mul (by exact_mod_cast hp0) (by exact_mod_cast hL0)]
  have hLpos' : 0 < L := by omega
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos'
  have hpos2 : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hlogA_ge : 2 * Real.log 2 + Real.log 3 ≤ Real.log A := by
    have hle : Real.log 12 ≤ Real.log A :=
      Real.log_le_log (show (0 : ℝ) < 12 by norm_num)
        (show (12 : ℝ) ≤ A by linarith only [hA12])
    rw [log_twelve] at hle
    exact hle
  have hslope : (1 : ℝ) < 6 * Real.log A * Real.log 2 := by
    have h2 := log_two_ge
    have h3 := log_three_ge
    have hAge : (7 / 3 : ℝ) ≤ Real.log A := by
      linarith only [hlogA_ge, h2, h3]
    have hposA : (0 : ℝ) ≤ Real.log A := le_trans (by norm_num) hAge
    have hmul : (7 / 3 : ℝ) * (2 / 3) ≤ Real.log A * Real.log 2 :=
      mul_le_mul hAge h2 (show (0 : ℝ) ≤ 2 / 3 by norm_num) hposA
    calc (1 : ℝ) < 28 / 3 := by norm_num
      _ ≤ 6 * ((7 / 3) * (2 / 3)) := by norm_num
      _ ≤ 6 * (Real.log A * Real.log 2) :=
        mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ 6 by norm_num)
      _ = 6 * Real.log A * Real.log 2 := by ring
  have hlogA_pos : (0 : ℝ) < Real.log A :=
    Real.log_pos (show (1 : ℝ) < A by linarith only [hA12])
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hE0 : p * L ≠ 0 := by omega
    rw [Nat.cast_zero, mul_zero, pow_zero, zero_pow hE0] at h
    norm_num at h
  · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set x1 : ℝ := 6 * A * Real.log A with hx1def
    have hx1pos : (0 : ℝ) < x1 := by
      rw [hx1def]
      exact mul_pos (mul_pos (show (0 : ℝ) < 6 by norm_num) hApos) hlogA_pos
    have hdiv : A / Real.log 2 ≤ x1 := by
      rw [hx1def, div_le_iff₀ hpos2]
      calc A = A * 1 := (mul_one A).symm
        _ ≤ A * (6 * Real.log A * Real.log 2) :=
          mul_le_mul_of_nonneg_left hslope.le hApos.le
        _ = 6 * A * Real.log A * Real.log 2 := by ring
    have hLApos : (0 : ℝ) < (L : ℝ) * A := mul_pos hLpos hApos
    have h12Lx1_eq : (12 : ℝ) * (L : ℝ) * x1 =
        72 * ((L : ℝ) * A) * Real.log A := by
      rw [hx1def]
      ring
    have hlog_base : Real.log (12 * (L : ℝ) * x1) =
        Real.log 72 + (Real.log L + Real.log A) +
          Real.log (Real.log A) := by
      have h72LA : ((72 : ℝ) * ((L : ℝ) * A)) ≠ 0 :=
        ne_of_gt (mul_pos (show (0 : ℝ) < 72 by norm_num) hLApos)
      have hlogA_ne : Real.log A ≠ 0 := ne_of_gt hlogA_pos
      have h72 : (72 : ℝ) ≠ 0 := by norm_num
      have hLA : ((L : ℝ) * A) ≠ 0 := ne_of_gt hLApos
      have hL : (L : ℝ) ≠ 0 := ne_of_gt hLpos
      rw [h12Lx1_eq, Real.log_mul h72LA hlogA_ne, Real.log_mul h72 hLA,
        Real.log_mul hL hAne]
    have hlp : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (show (0 : ℝ) < 2 by norm_num)
        (show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp)
    have hll : (0 : ℝ) ≤ Real.log (L : ℝ) :=
      Real.log_nonneg (show (1 : ℝ) ≤ (L : ℝ) by exact_mod_cast hL1)
    have hsum : (4 : ℝ) ≤ Real.log (p : ℝ) + 2 * Real.log (L : ℝ) := by
      have e1 : (((p * L ^ 2 : ℕ)) : ℝ) = (p : ℝ) * ((L : ℝ)) ^ 2 := by
        push_cast
        ring
      have hpl2 : Real.log (((p * L ^ 2 : ℕ)) : ℝ) =
          Real.log (p : ℝ) + 2 * Real.log (L : ℝ) := by
        rw [e1, Real.log_mul (by exact_mod_cast hp0)
          (ne_of_gt (pow_pos hLpos 2)), Real.log_pow]
        norm_num
      have hge : Real.log 72 ≤ Real.log (((p * L ^ 2 : ℕ)) : ℝ) :=
        Real.log_le_log (show (0 : ℝ) < 72 by norm_num)
          (show (72 : ℝ) ≤ (((p * L ^ 2 : ℕ)) : ℝ) by exact_mod_cast hpL)
      have h4 : (4 : ℝ) ≤ Real.log 72 := by
        rw [log_seventy_two]
        linarith only [log_two_ge, log_three_ge]
      rw [hpl2] at hge
      linarith only [hge, h4]
    have hy : (0 : ℝ) < Real.log (p : ℝ) + Real.log (L : ℝ) := by
      have h2pos : (0 : ℝ) < Real.log 2 :=
        Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      linarith only [hlp, hll, h2pos]
    have hbase : (0 : ℝ) ≤
        x1 * Real.log 2 - A * Real.log (12 * (L : ℝ) * x1) := by
      have hform : x1 * Real.log 2 - A * Real.log (12 * (L : ℝ) * x1) =
          A * (6 * Real.log A * Real.log 2 -
            Real.log (12 * (L : ℝ) * x1)) := by
        rw [hx1def]
        ring
      rw [hform]
      apply mul_nonneg hApos.le
      rw [hlog_base, hlogA_eq]
      have hcore := base_inequality (Real.log (p : ℝ)) (Real.log (L : ℝ))
        hlp hll hsum hy
      linarith only [hcore]
    have h2npos : (0 : ℝ) < (2 : ℝ) ^ n :=
      pow_pos (show (0 : ℝ) < 2 by norm_num) n
    have hlog_n : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    have hlog_rhs : Real.log ((12 * (L : ℝ) * (n : ℝ)) ^ (p * L)) =
        A * Real.log (12 * (L : ℝ) * (n : ℝ)) := by
      rw [Real.log_pow, ← hAdef]
    have hle : (n : ℝ) * Real.log 2 ≤
        A * Real.log (12 * (L : ℝ) * (n : ℝ)) := by
      have hmono : Real.log ((2 : ℝ) ^ n) ≤
          Real.log ((12 * (L : ℝ) * (n : ℝ)) ^ (p * L)) :=
        Real.log_le_log h2npos h
      rw [hlog_n, hlog_rhs] at hmono
      exact hmono
    by_contra hcon
    rw [not_le] at hcon
    have hslope_lt := slope_strict_mono A (Real.log 2) x1 (n : ℝ)
      hA1 hpos2 hdiv hcon hx1pos
    have hCpos : (0 : ℝ) < 12 * (L : ℝ) :=
      mul_pos (show (0 : ℝ) < 12 by norm_num) hLpos
    have hshift1 : Real.log (12 * (L : ℝ) * x1) =
        Real.log (12 * (L : ℝ)) + Real.log x1 :=
      Real.log_mul (ne_of_gt hCpos) (ne_of_gt hx1pos)
    have hshift2 : Real.log (12 * (L : ℝ) * (n : ℝ)) =
        Real.log (12 * (L : ℝ)) + Real.log (n : ℝ) :=
      Real.log_mul (ne_of_gt hCpos) (ne_of_gt hn_pos)
    have hgt : x1 * Real.log 2 - A * Real.log (12 * (L : ℝ) * x1) <
        (n : ℝ) * Real.log 2 - A * Real.log (12 * (L : ℝ) * (n : ℝ)) := by
      rw [hshift1, hshift2]
      linarith only [hslope_lt]
    have hle' : (n : ℝ) * Real.log 2 - A * Real.log (12 * (L : ℝ) * (n : ℝ)) ≤
        0 := by
      linarith only [hle]
    linarith only [hbase, hgt, hle']

/-- VC corollary for any Boolean class with a BHLM-shaped growth
bound. The growth hypothesis starts at `n = 1`: at `n = 0` the
right side is `0` while `growthFunction C 0 = 1` for a nonempty
class. -/
theorem vcDim_le_of_growthFunction_le_bhlm {α : Type*}
    (C : ConceptClass α Bool) (p L : ℕ) (hp : 2 ≤ p)
    (hpL : 72 ≤ p * L ^ 2)
    (hgrowth : ∀ n, 1 ≤ n →
      (growthFunction C n : ℝ) ≤ (12 * (n : ℝ) * (L : ℝ)) ^ (p * L)) :
    HasFiniteVCDim C ∧
      (vcDim C : ℝ) ≤ 6 * ((p * L : ℕ) : ℝ) * Real.log ((p * L : ℕ) : ℝ) := by
  have hL1 : 1 ≤ L := bhlm_L_ge_one p L hpL
  have h12 : 12 ≤ p * L := bhlm_pL_ge_twelve p L hp hpL
  have hB0 : (0 : ℝ) ≤
      6 * ((p * L : ℕ) : ℝ) * Real.log ((p * L : ℕ) : ℝ) := by
    have hA1 : (1 : ℝ) ≤ ((p * L : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ p * L by omega)
    have hlog : (0 : ℝ) ≤ Real.log ((p * L : ℕ) : ℝ) :=
      Real.log_nonneg hA1
    exact mul_nonneg
      (mul_nonneg (show (0 : ℝ) ≤ 6 by norm_num) (Nat.cast_nonneg _)) hlog
  have hkey : ∀ k ∈ {n : ℕ | ∃ W : Finset α,
      W.card = n ∧ SetShatters C (↑W)},
      (k : ℝ) ≤ 6 * ((p * L : ℕ) : ℝ) * Real.log ((p * L : ℕ) : ℝ) := by
    rintro k ⟨W, rfl, hW⟩
    by_cases hk0 : W.card = 0
    · rw [hk0]
      simpa using hB0
    · have hk1 : 1 ≤ W.card := by omega
      have hcard := setShatters_iff_card_traceFamily.mp hW
      have hle := traceFamily_card_le_growthFunction C W
      have hnat : 2 ^ W.card ≤ growthFunction C W.card := by
        rw [← hcard]
        exact hle
      have hreal : (2 : ℝ) ^ W.card ≤ (growthFunction C W.card : ℝ) := by
        exact_mod_cast hnat
      have hg := hgrowth W.card hk1
      have hcomb : (2 : ℝ) ^ W.card ≤
          (12 * ((W.card : ℕ) : ℝ) * (L : ℝ)) ^ (p * L) :=
        le_trans hreal hg
      exact le_six_mul_log_of_two_pow_le_bhlm p L W.card hp hpL hcomb
  have hfin : HasFiniteVCDim C := by
    obtain ⟨N, hN⟩ :=
      exists_nat_ge (6 * ((p * L : ℕ) : ℝ) * Real.log ((p * L : ℕ) : ℝ))
    refine hasFiniteVCDim_iff.mpr ⟨N, fun W hW => ?_⟩
    have hnum := hkey W.card ⟨W, rfl, hW⟩
    exact Nat.cast_le.mp (le_trans hnum hN)
  refine ⟨hfin, ?_⟩
  by_cases hne : {n : ℕ | ∃ W : Finset α,
      W.card = n ∧ SetShatters C (↑W)}.Nonempty
  · obtain ⟨W, hWc, hW⟩ := Nat.sSup_mem hne hfin
    have hnum := hkey W.card ⟨W, rfl, hW⟩
    have heq : vcDim C = W.card := by
      unfold vcDim
      exact hWc.symm
    rw [heq]
    exact hnum
  · have hSeq : {n : ℕ | ∃ W : Finset α,
        W.card = n ∧ SetShatters C (↑W)} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    have hV : vcDim C = 0 := by
      unfold vcDim
      rw [hSeq]
      simp
    rw [hV]
    simpa using hB0

end Cslib.MachineLearning.PACLearning

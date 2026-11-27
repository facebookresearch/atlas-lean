/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HeightOneMultipleZetaSeries
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Bounds

/-! # Height one multiple zeta series with negative integer weights

The finite elementary-symmetric expansion for each largest index gives the signed
binomial coefficients. The corresponding expansion with positive weights gives
an absolute majorant for exchanging the two sums.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

private noncomputable def reciprocalCoeff (K : Type*) [Field K] (a j : ℕ) : K :=
  ∑ T ∈ (Icc 1 a).powersetCard j, ∏ i ∈ T, (1 / (i : K))

private lemma reciprocalCoeff_eq_zero (K : Type*) [Field K] {a j : ℕ} (h : a < j) :
    reciprocalCoeff K a j = 0 := by
  rw [reciprocalCoeff, powersetCard_eq_empty.mpr (by simpa using h), sum_empty]

private lemma sum_reciprocalCoeff_mul_pow {K : Type*} [Field K] (a : ℕ) (t : K) :
    ∑ j ∈ range (a + 1), reciprocalCoeff K a j * t ^ j =
      ∏ i ∈ Icc 1 a, (1 + t / (i : K)) := by
  symm
  rw [show (∏ i ∈ Icc 1 a, (1 + t / (i : K))) = ∏ i ∈ Icc 1 a, (t / (i : K) + 1) from
    prod_congr rfl fun _ _ => add_comm _ _, prod_add]
  simp only [prod_const_one, mul_one]
  rw [sum_powerset]
  simp only [Nat.card_Icc, Nat.add_sub_cancel]
  apply sum_congr rfl
  intro j _
  rw [reciprocalCoeff, sum_mul]
  apply sum_congr rfl
  intro T hT
  simp only [div_eq_mul_inv, one_mul, prod_mul_distrib, prod_const, (mem_powersetCard.mp hT).2]
  rw [mul_comm]

private lemma norm_reciprocalCoeff (a j : ℕ) :
    ‖reciprocalCoeff ℂ a j‖ = reciprocalCoeff ℝ a j := by
  have hcast : ((reciprocalCoeff ℝ a j : ℝ) : ℂ) = reciprocalCoeff ℂ a j := by
    simp [reciprocalCoeff]
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  unfold reciprocalCoeff
  positivity

-- This binomial coefficient is the factorial ratio `(a + r)! / (a! * r!)`.
private lemma prod_one_add_nat_div (a r : ℕ) :
    ∏ i ∈ Icc 1 a, (1 + (r : ℝ) / (i : ℝ)) = ((a + r).choose a : ℝ) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [prod_Icc_succ_top (by omega : 1 ≤ a + 1), ih,
      show a + 1 + r = (a + r) + 1 by omega]
    have h : (((a + r + 1 : ℕ) : ℝ)) * ((a + r).choose a : ℝ) =
        (((a + r + 1).choose (a + 1) : ℕ) : ℝ) * ((a + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (a + r) a
    push_cast at h ⊢
    field_simp
    linarith only [h]

private lemma prod_one_sub_nat_succ_div (q a : ℕ) :
    ∏ i ∈ Icc 1 a, (1 - ((q : ℂ) + 1) / (i : ℂ)) = (q.choose a : ℂ) * (-1) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [prod_Icc_succ_top (by omega : 1 ≤ a + 1), ih]
    by_cases h : a ≤ q
    · have hstep : (q.choose (a + 1) : ℂ) * ((a + 1 : ℕ) : ℂ) =
          (q.choose a : ℂ) * ((q - a : ℕ) : ℂ) := by
        exact_mod_cast Nat.choose_succ_right_eq q a
      push_cast [Nat.cast_sub h] at hstep ⊢
      rw [pow_succ]
      field_simp
      linear_combination hstep
    · simp [Nat.choose_eq_zero_of_lt (by omega : q < a),
        Nat.choose_eq_zero_of_lt (by omega : q < a + 1)]

private lemma tsum_heightOne_mul_neg (r : ℕ) (s : ℂ) (hs : (r : ℝ) + 1 < s.re) :
    ∑' j : ℕ, heightOneMultipleZeta s j * (-(r : ℂ)) ^ j =
      ∑' a : ℕ, ((a : ℂ) + 1) ^ (-s) * ∏ i ∈ Icc 1 a, (1 - (r : ℂ) / (i : ℂ)) := by
  let F (a j : ℕ) : ℂ := ((a : ℂ) + 1) ^ (-s) * (reciprocalCoeff ℂ a j * (-(r : ℂ)) ^ j)
  have hfin (a j : ℕ) (hj : j ∉ range (a + 1)) : F a j = 0 := by
    simp [F, reciprocalCoeff_eq_zero ℂ (by simpa using hj : a < j)]
  have hnorm (a j : ℕ) : ‖F a j‖ =
      ((a : ℝ) + 1) ^ (-s.re) * (reciprocalCoeff ℝ a j * (r : ℝ) ^ j) := by
    have hbase : (a : ℂ) + 1 = (((a : ℝ) + 1 : ℝ) : ℂ) := by simp
    dsimp only [F]
    rw [norm_mul, hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re, norm_mul, norm_reciprocalCoeff, norm_pow, norm_neg,
      Complex.norm_natCast]
  have hrow (a : ℕ) : ∑' j, ‖F a j‖ = ((a : ℝ) + 1) ^ (-s.re) * ((a + r).choose a : ℝ) := by
    rw [tsum_eq_sum (s := range (a + 1)) (fun j hj => by rw [hfin a j hj, norm_zero])]
    simp_rw [hnorm, ← mul_sum, sum_reciprocalCoeff_mul_pow, prod_one_add_nat_div]
  have hmajor : Summable (fun a : ℕ => ((r : ℝ) + 1) ^ r * ((a : ℝ) + 1) ^ ((r : ℝ) - s.re)) := by
    have hp := Real.summable_nat_rpow.mpr (show (r : ℝ) - s.re < -1 by linarith)
    simpa only [Nat.cast_add, Nat.cast_one] using ((summable_nat_add_iff 1).2 hp).mul_left
      (((r : ℝ) + 1) ^ r)
  have hnormsum : Summable (fun p : ℕ × ℕ => ‖F p.1 p.2‖) := by
    refine (summable_prod_of_nonneg (fun p => norm_nonneg (F p.1 p.2))).2 ⟨fun a => ?_, ?_⟩
    · apply summable_of_ne_finset_zero (s := range (a + 1))
      intro j hj
      rw [hfin a j hj, norm_zero]
    · apply hmajor.of_nonneg_of_le (fun a => tsum_nonneg fun j => norm_nonneg (F a j))
      intro a
      have hchoose : ((a + r).choose a : ℝ) ≤ (((a : ℝ) + 1) * ((r : ℝ) + 1)) ^ r := by
        rw [Nat.choose_symm_add]
        have h : ((a + r).choose r : ℝ) ≤ ((a : ℝ) + r) ^ r := by
          exact_mod_cast Nat.choose_le_pow (a + r) r
        refine h.trans (pow_le_pow_left₀ (by positivity) ?_ _)
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (Nat.cast_nonneg (α := ℝ) r)]
      rw [hrow]
      calc
        _ ≤ ((a : ℝ) + 1) ^ (-s.re) * (((a : ℝ) + 1) * ((r : ℝ) + 1)) ^ r := by gcongr
        _ = _ := by
          rw [mul_pow, ← mul_assoc, ← Real.rpow_natCast ((a : ℝ) + 1),
            ← Real.rpow_add (by positivity), add_comm (-s.re), mul_comm]
          rfl
  have hsum : Summable (Function.uncurry F) := hnormsum.of_norm_bounded fun _ => le_rfl
  calc
    _ = ∑' j, ∑' a, F a j := by
      refine tsum_congr (fun j => ?_)
      rw [heightOneMultipleZeta, ← tsum_mul_right]
      exact tsum_congr (fun a => mul_assoc _ _ _)
    _ = ∑' a, ∑' j, F a j := hsum.tsum_comm
    _ = _ := by
      refine tsum_congr (fun a => ?_)
      rw [tsum_eq_sum (s := range (a + 1)) (hfin a)]
      dsimp only [F]
      rw [← mul_sum, sum_reciprocalCoeff_mul_pow]
      simp only [neg_div, ← sub_eq_add_neg]

private lemma tsum_heightOne_mul_neg_binomial (r : ℕ) (hr : 1 ≤ r) (s : ℂ)
    (hs : (r : ℝ) + 1 < s.re) :
    ∑' j : ℕ, heightOneMultipleZeta s j * (-(r : ℂ)) ^ j =
      ∑ m ∈ range r, ((r - 1).choose m : ℂ) * (-1) ^ m * ((m : ℂ) + 1) ^ (-s) := by
  rw [tsum_heightOne_mul_neg r s hs, tsum_eq_sum (s := range r)]
  · refine sum_congr rfl (fun m _ => ?_)
    have hr' : (r : ℂ) = ((r - 1 : ℕ) : ℂ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hr).symm
    rw [hr', prod_one_sub_nat_succ_div]
    ac_rfl
  · intro a ha
    have hm : r ∈ Icc 1 a := mem_Icc.mpr ⟨hr, by simpa using ha⟩
    rw [prod_eq_zero hm, mul_zero]
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
    simp [hr0]

/-- **Height one multiple zeta series weighted by powers of a negative integer.** Let $r \ge 1$
be an integer and let $\zeta(s, \{1\}^j)$ denote the height one multiple zeta function. For
every complex number $s$ with $\operatorname{Re} s > r + 1$,

$$\sum_{j \ge 0} \zeta(s, \{1\}^j) (-r)^j = \sum_{m=0}^{r-1} \binom{r-1}{m} (-1)^m (m+1)^{-s}.$$

For every integer $k > r + 1$,

$$\sum_{j \ge 0} \zeta(k, \{1\}^j) (-r)^j = \frac{H_{r,k-1}}{r},$$

where $H_{r,k-1} = \sum_{i=1}^{r} (-1)^{i-1} \binom{r}{i} i^{-(k-1)}$ is the rational Roman
harmonic number (Equation (2.18)).

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Corollary 2 (`integers-2024-A43-cor-2`). -/
public theorem tsum_heightOneMultipleZeta_mul_neg_nat_pow
    (r : ℕ) (hr : 1 ≤ r) :
    (∀ s : ℂ, (r : ℝ) + 1 < s.re →
      ∑' j : ℕ, heightOneMultipleZeta s j * (-(r : ℂ)) ^ j =
        ∑ m ∈ Finset.range r, ((r - 1).choose m : ℂ) * (-1) ^ m * ((m : ℂ) + 1) ^ (-s)) ∧
    ∀ k : ℕ, r + 1 < k →
      ∑' j : ℕ, heightOneMultipleZeta k j * (-(r : ℂ)) ^ j =
        (((∑ i ∈ Finset.Icc 1 r, (-1 : ℚ) ^ (i - 1) * (r.choose i : ℚ) / (i : ℚ) ^ (k - 1)) /
          r : ℚ) : ℂ) := by
  refine ⟨tsum_heightOne_mul_neg_binomial r hr, fun k hk => ?_⟩
  have hks : (r : ℝ) + 1 < (k : ℂ).re := by
    simpa only [Complex.natCast_re, Nat.cast_add, Nat.cast_one] using
      (show ((r + 1 : ℕ) : ℝ) < (k : ℝ) by exact_mod_cast hk)
  rw [tsum_heightOne_mul_neg_binomial r hr k hks]
  rw [show Icc 1 r = Ico 1 (r + 1) by ext i; simp, sum_Ico_eq_sum_range,
    Nat.add_sub_cancel, Rat.cast_div, Rat.cast_sum, sum_div]
  refine sum_congr rfl (fun m _ => ?_)
  simp only [Nat.add_comm 1 m, Nat.add_sub_cancel, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_add, Rat.cast_one, Nat.cast_add,
    Nat.cast_one, Complex.cpow_neg, Complex.cpow_natCast]
  have hc : (r : ℂ) * ((r - 1).choose m : ℂ) = (r.choose (m + 1) : ℂ) * ((m : ℂ) + 1) := by
    have h := Nat.add_one_mul_choose_eq (r - 1) m
    rw [Nat.sub_add_cancel hr] at h
    exact_mod_cast h
  have hp : ((m : ℂ) + 1) ^ k = ((m : ℂ) + 1) ^ (k - 1) * ((m : ℂ) + 1) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  rw [hp]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hm0 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp [hr0, hm0]
  linear_combination hc

end

end MetaMathlibExt

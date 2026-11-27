/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The odd-weighted Catalan series

Expand each reciprocal difference in the digamma series into a sum of rising factorial ratios.
Summing the resulting double series in the opposite order gives the Catalan coefficients.
-/

open Filter Finset Topology

namespace MetaMathlibExt

namespace OddWeightedCatalanSeries

private def ratio {K : Type*} [Field K] (w : K) (n : ℕ) : K :=
  ∏ j ∈ range n, (1 / 2 + j : K) / (w + j)

private def term {K : Type*} [Field K] (w : K) (n : ℕ) : K :=
  ratio w (n + 1) / (w + (n + 1 : ℕ))

private lemma ratio_succ {K : Type*} [Field K] (w : K) (n : ℕ) :
    ratio w (n + 1) = ratio w n * ((1 / 2 + n) / (w + n)) :=
  prod_range_succ _ _

private lemma ratio_norm_le {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    ‖ratio w n‖ ≤ ratio w.re n := by
  unfold ratio
  rw [norm_prod]
  refine prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ ?_
  have h : 0 < w.re + j := by positivity
  have hle := Complex.re_le_norm (w + j)
  simp only [Complex.add_re, Complex.natCast_re] at hle
  have heq : (1 / 2 + j : ℂ) = ((1 / 2 + j : ℝ) : ℂ) := by push_cast; rfl
  rw [norm_div, heq, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left (by positivity) h hle

private lemma term_norm_le {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    ‖term w n‖ ≤ term w.re n := by
  unfold term
  rw [norm_div]
  have hle := Complex.re_le_norm (w + (n + 1 : ℕ))
  simp only [Complex.add_re, Complex.natCast_re] at hle
  exact (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hle).trans
    (div_le_div_of_nonneg_right (ratio_norm_le hw _) (by positivity))

private lemma ratio_real_tendsto {x : ℝ} (hx : 1 / 2 < x) :
    Tendsto (fun n ↦ ratio x (n + 1)) atTop (𝓝 0) := by
  have hΓ := (Real.GammaSeq_tendsto_Gamma x).div (Real.GammaSeq_tendsto_Gamma (1 / 2))
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have hp := (tendsto_rpow_neg_atTop (sub_pos.mpr hx)).comp tendsto_natCast_atTop_atTop
  have h := hΓ.mul hp
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hprod : (∏ j ∈ range (n + 1), (1 / 2 + j : ℝ)) ≠ 0 :=
    (prod_pos fun j _ ↦ by positivity).ne'
  have hx' : 0 < x := by linarith
  have hw : (∏ j ∈ range (n + 1), (x + j)) ≠ 0 := (prod_pos fun j _ ↦ by positivity).ne'
  change Real.GammaSeq x n / Real.GammaSeq (1 / 2) n * (n : ℝ) ^ (-(x - 1 / 2)) = _
  rw [neg_sub, Real.rpow_sub hn', Real.GammaSeq, Real.GammaSeq, ratio, prod_div_distrib]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp [Real.rpow_pos_of_pos hn', hf, hprod, hw]

private lemma ratio_tendsto {w : ℂ} (hw : 1 / 2 < w.re) :
    Tendsto (fun n ↦ ratio w (n + 1)) atTop (𝓝 0) :=
  squeeze_zero_norm (fun n ↦ ratio_norm_le (by linarith : 0 < w.re) (n + 1))
    (ratio_real_tendsto hw)

-- Summation in the index of the rising factorial ratio.
private lemma row_partial {K : Type*} [Field K] [CharZero K] {w : K}
    (hw : ∀ n : ℕ, w + n ≠ 0) (hw' : w - 1 / 2 ≠ 0) (N : ℕ) :
    ∑ n ∈ range N, term w n =
      1 / (w - 1 / 2) - 1 / w - ratio w (N + 1) / (w - 1 / 2) := by
  have h (n : ℕ) : term w n =
      ratio w (n + 1) / (w - 1 / 2) - ratio w (n + 1 + 1) / (w - 1 / 2) := by
    rw [ratio_succ w (n + 1), term]
    have hn := hw (n + 1)
    generalize (1 / 2 : K) = a at hw' ⊢
    field_simp [hn, hw']
    ring
  simp_rw [h]
  rw [sum_range_sub' (fun n ↦ ratio w (n + 1) / (w - 1 / 2))]
  apply congrArg (· - ratio w (N + 1) / (w - 1 / 2))
  simp only [zero_add, ratio, prod_range_one, Nat.cast_zero, add_zero]
  have hw0 : w ≠ 0 := by simpa using hw 0
  generalize (1 / 2 : K) = a at hw' ⊢
  field_simp [hw0, hw']
  ring

private lemma add_nat_ne {w : ℂ} (hw : 0 < w.re) (n : ℕ) : w + n ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [Nat.cast_nonneg (α := ℝ) n]

private lemma gap_hasSum {z : ℂ} (hz : 1 / 2 < z.re) :
    HasSum (fun k : ℕ ↦ 1 / (z + k - 1 / 2) - 1 / (z + k))
      (Complex.digamma z - Complex.digamma (z - 1 / 2)) := by
  have hp {w : ℂ} (hw : 0 < w.re) (m : ℕ) : w ≠ -m :=
    fun h ↦ add_nat_ne hw m (by rw [h]; simp)
  have hz' : 0 < (z - 1 / 2).re := by norm_num; linarith
  have hs := (Complex.hasSum_digamma_series (z + 1) (by simp; linarith)).sub
    (Complex.hasSum_digamma_series (z - 1 / 2 + 1) (by simp; linarith))
  rw [Complex.digamma_apply_add_one _ (hp (by linarith : 0 < z.re)),
    Complex.digamma_apply_add_one _ (hp hz')] at hs
  rw [← hasSum_nat_add_iff' 1]
  convert hs.congr_fun (g := fun k : ℕ ↦ 1 / (z + (k + 1 : ℕ) - 1 / 2) -
    1 / (z + (k + 1 : ℕ))) (fun k ↦ by unfold Complex.digammaSeriesTerm; push_cast; ring_nf) using 1
  simp only [sum_range_one, Nat.cast_zero, add_zero, one_div]
  ring

private lemma row_real {x : ℝ} (hx : 1 / 2 < x) :
    HasSum (term x) (1 / (x - 1 / 2) - 1 / x) := by
  have hx' : 0 < x := by linarith
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _).2
  · simp_rw [row_partial (w := x) (fun n ↦ by positivity) (sub_ne_zero.mpr hx.ne')]
    simpa using (tendsto_const_nhds (x := 1 / (x - 1 / 2) - 1 / x)).sub
      ((ratio_real_tendsto hx).div_const (x - 1 / 2))
  · unfold term ratio
    positivity

private lemma summable_terms {z : ℂ} (hz : 1 / 2 < z.re) :
    Summable (fun p : ℕ × ℕ ↦ term (z + p.1) p.2) := by
  have hx (k : ℕ) : 1 / 2 < z.re + k := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have houter : Summable (fun k : ℕ ↦ 1 / (z.re + k - 1 / 2) - 1 / (z.re + k)) := by
    apply Complex.summable_ofReal.mp
    push_cast
    exact (gap_hasSum (z := (z.re : ℂ)) hz).summable
  have hmajor : Summable (fun p : ℕ × ℕ ↦ term (z.re + p.1) p.2) := by
    apply (summable_prod_of_nonneg ?_).2
    · refine ⟨fun k ↦ (row_real (hx k)).summable, ?_⟩
      simpa only [(row_real (hx _)).tsum_eq] using houter
    · intro p
      have hpos : 0 < z.re := by linarith
      unfold term ratio
      positivity
  refine hmajor.of_norm_bounded fun p ↦ ?_
  simpa using term_norm_le (w := z + p.1) (by simp; linarith [hx p.1]) p.2

private lemma row_sum {w : ℂ} (hw : 1 / 2 < w.re) (hs : Summable (term w)) :
    HasSum (term w) (1 / (w - 1 / 2) - 1 / w) := by
  have hne : w - 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  apply hs.hasSum_iff_tendsto_nat.mpr
  simp_rw [row_partial (add_nat_ne (by linarith : 0 < w.re)) hne]
  simpa using (tendsto_const_nhds (x := 1 / (w - 1 / 2) - 1 / w)).sub
    ((ratio_tendsto hw).div_const (w - 1 / 2))

-- A unit shift cancels all but the two endpoint factors in the denominator.
private lemma ratio_shift {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    ratio (w + 1) n * (w + n) = ratio w n * w := by
  induction n with
  | zero => simp [ratio]
  | succ n ih =>
    rw [ratio_succ, ratio_succ, Nat.cast_succ]
    have h := add_nat_ne hw n
    have h' := add_nat_ne (w := w + 1) (by simp; linarith) n
    rw [show w + (n + 1) = w + 1 + n by ring]
    field_simp [h, h']
    linear_combination (1 + 2 * (n : ℂ)) * ih

private lemma ratio_shift_tendsto {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    Tendsto (fun k : ℕ ↦ ratio (z + k) (n + 1)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun k : ℕ ↦ ratio (z.re + k) (n + 1))
  · intro k
    have hw : 0 < (z + k).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      positivity
    simpa using ratio_norm_le hw (n + 1)
  · have h (j : ℕ) : Tendsto (fun k : ℕ ↦ (1 / 2 + j : ℝ) / (z.re + k + j)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop <|
        (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds
    simpa [ratio] using tendsto_finsetProd (range (n + 1)) (fun j _ ↦ h j)

private lemma column_sum {z : ℂ} (hz : 0 < z.re) (n : ℕ)
    (hs : Summable (fun k : ℕ ↦ term (z + k) n)) :
    HasSum (fun k : ℕ ↦ term (z + k) n) (ratio z (n + 1) / (n + 1 : ℕ)) := by
  have h (k : ℕ) : term (z + k) n =
      ratio (z + k) (n + 1) / (n + 1 : ℕ) -
        ratio (z + (k + 1 : ℕ)) (n + 1) / (n + 1 : ℕ) := by
    have hw : 0 < (z + k).re := by
      simpa only [Complex.add_re, Complex.natCast_re] using
        add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg k)
    have hshift := ratio_shift hw (n + 1)
    rw [Nat.cast_succ k, ← add_assoc]
    unfold term
    have hne := add_nat_ne hw (n + 1)
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [hne, hn]
    linear_combination hshift
  apply hs.hasSum_iff_tendsto_nat.mpr
  simp_rw [h, sum_range_sub' (fun k : ℕ ↦ ratio (z + k) (n + 1) / (n + 1 : ℕ))]
  simpa using (tendsto_const_nhds (x := ratio z (n + 1) / (n + 1 : ℕ))).sub
    ((ratio_shift_tendsto hz n).div_const ((n + 1 : ℕ) : ℂ))

-- Clearing the generalized binomial denominator leaves the central binomial recurrence.
private lemma coefficient {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    2 * z * ratio z (n + 1) * (∏ j ∈ Icc 1 n, (z + j) / j) * 4 ^ n =
      (2 * (n : ℂ) + 1) * n.centralBinom := by
  induction n with
  | zero =>
    have h : z ≠ 0 := by simpa using add_nat_ne hz 0
    simp [ratio]
    field_simp [h]
  | succ n ih =>
    rw [ratio_succ z (n + 1), prod_Icc_succ_top (by omega : 1 ≤ n + 1), pow_succ]
    have hne := add_nat_ne hz (n + 1)
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    calc
      _ = (2 * z * ratio z (n + 1) * (∏ j ∈ Icc 1 n, (z + j) / j) * 4 ^ n) *
          ((2 * (n + 1 : ℕ) + 1) * 2 / (n + 1 : ℕ)) := by
            field_simp [hne, hn]
            ring
      _ = _ := by
        rw [ih]
        have h : ((n + 1 : ℕ) : ℂ) * (n + 1).centralBinom =
            2 * (2 * (n : ℂ) + 1) * n.centralBinom := by
          exact_mod_cast Nat.succ_mul_centralBinom_succ n
        field_simp [hn]
        linear_combination -(2 * ((n + 1 : ℕ) : ℂ) + 1) * h

private lemma catalan_term {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    (2 * (n : ℂ) + 1) * catalan n / (4 ^ n * ∏ j ∈ Icc 1 n, (z + j) / j) =
      (2 * z) * (ratio z (n + 1) / (n + 1 : ℕ)) := by
  have hprod : (∏ j ∈ Icc 1 n, (z + j) / j) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j hj
    have hj' : 0 < j := (mem_Icc.mp hj).1
    exact div_ne_zero (add_nat_ne hz j) (by exact_mod_cast hj'.ne')
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hc : ((n + 1 : ℕ) : ℂ) * catalan n = n.centralBinom := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have h := coefficient hz n
  rw [← hc] at h
  field_simp [hn, hprod]
  linear_combination -h

end OddWeightedCatalanSeries

open OddWeightedCatalanSeries

/-- **Digamma evaluation of the $(2n+1)$-weighted Catalan series with binomial denominators.**
Let $C_n$ be the $n$-th Catalan number and $\psi$ the digamma function, and for complex $z$ write
$\binom{n+z}{n} = \prod_{j=1}^{n} (z+j)/j$. For every complex number $z$ with
$\operatorname{Re} z > 1/2$,
$$\sum_{n=0}^{\infty} \frac{(2n+1)\,C_n}{4^n \binom{n+z}{n}} =
2z\bigl(\psi(z) - \psi(z - \tfrac12)\bigr).$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 5, identity (11) (`integers-2025-A18-thm-5`). -/
public theorem tsum_odd_mul_catalan_div_four_pow_mul_binom {z : ℂ} (hz : 1 / 2 < z.re) :
    ∑' n : ℕ, (2 * (n : ℂ) + 1) * catalan n / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      2 * z * (Complex.digamma z - Complex.digamma (z - 1 / 2)) := by
  have hs := summable_terms hz
  have hrow (k : ℕ) := row_sum (w := z + k)
    (by simp; linarith [Nat.cast_nonneg (α := ℝ) k]) (hs.prod_factor k)
  have hcol (n : ℕ) := column_sum (z := z) (by linarith) n (hs.prod_symm.prod_factor n)
  have hexchange := Summable.tsum_comm (f := fun k n : ℕ ↦ term (z + k) n) hs
  simp_rw [(hrow _).tsum_eq, (hcol _).tsum_eq] at hexchange
  simp_rw [catalan_term (by linarith : 0 < z.re)]
  rw [tsum_mul_left, hexchange, (gap_hasSum hz).tsum_eq]

end MetaMathlibExt

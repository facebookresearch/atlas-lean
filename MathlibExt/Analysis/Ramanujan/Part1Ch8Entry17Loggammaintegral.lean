/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Defs
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Basic

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry17Loggammaintegral

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry17Term (x : ℝ) (j : ℕ) : ℝ :=
  let k : ℝ := j + 1
  Real.log k / k - Real.log (k + x) / (k + x)

def chapter8Entry17Phi (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter8Entry17Term x j

def chapter8RealDigamma (x : ℝ) : ℝ :=
  deriv Real.Gamma x / Real.Gamma x

private theorem chapter8_aux_pos1 (x : ℝ) (hx : -1 < x) :
    ∀ j : ℕ, 0 < (j + 1 : ℝ) + x := by
  intro j
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

private theorem chapter8_aux_pos2 (x : ℝ) (n : ℕ) (hx : -1 < x) (hn : 0 < n) :
    ∀ k ∈ Finset.range n, ∀ j : ℕ, 0 < (j + 1 : ℝ) + (x - k) / n := by
  intro k hk j
  rw [Finset.mem_range] at hk
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hkn : (k : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : k + 1 ≤ n := hk
    have h2 : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hxkn : (-1 : ℝ) < (x - (k : ℝ)) / (n : ℝ) := by
    rw [lt_div_iff₀ hnR]
    nlinarith
  linarith

private theorem chapter8_aux_gamma (x : ℝ) (hx : -1 < x) :
    0 < Real.Gamma (x + 1) := by
  apply Real.Gamma_pos_of_pos
  linarith

/-- For `|t| ≤ 1/2`, `|log (1 + t)| ≤ 2 * |t|`. -/
private theorem chapter8_log_one_add_bound {t : ℝ} (ht : |t| ≤ 1 / 2)
    (hpos : 0 < 1 + t) : |Real.log (1 + t)| ≤ 2 * |t| := by
  have ⟨ht_lo, ht_hi⟩ := abs_le.mp ht
  by_cases ht_nonneg : 0 ≤ t
  · have h1 : (1 : ℝ) ≤ 1 + t := by linarith
    have hlog_nonneg : 0 ≤ Real.log (1 + t) := Real.log_nonneg h1
    have hle0 : Real.log (1 + t) ≤ (1 + t) - 1 :=
      Real.log_le_sub_one_of_pos hpos
    have hle : Real.log (1 + t) ≤ t := by linarith
    have habs_t : |t| = t := abs_of_nonneg ht_nonneg
    have habs_log : |Real.log (1 + t)| = Real.log (1 + t) :=
      abs_of_nonneg hlog_nonneg
    rw [habs_log, habs_t]
    linarith
  · push Not at ht_nonneg
    have hlog_nonpos : Real.log (1 + t) ≤ 0 :=
      Real.log_nonpos (le_of_lt hpos) (by linarith)
    have habs_log : |Real.log (1 + t)| = -Real.log (1 + t) :=
      abs_of_nonpos hlog_nonpos
    have habs_t : |t| = -t := abs_of_neg ht_nonneg
    rw [habs_log, habs_t]
    have hinv_pos : (0 : ℝ) < (1 + t)⁻¹ := inv_pos.mpr hpos
    have hle0 : Real.log ((1 + t)⁻¹) ≤ (1 + t)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos hinv_pos
    rw [Real.log_inv] at hle0
    have hne : (1 + t : ℝ) ≠ 0 := ne_of_gt hpos
    have heq : (1 + t)⁻¹ - 1 = -t / (1 + t) := by
      field_simp
      ring
    have hinv_le : (1 + t)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      linarith
    have hnt_nonneg : (0 : ℝ) ≤ -t := by linarith
    have hmul : -t / (1 + t) ≤ 2 * (-t) := by
      rw [div_eq_mul_inv]
      have h := mul_le_mul_of_nonneg_left hinv_le hnt_nonneg
      linarith [h]
    linarith [hle0, heq, hmul]

/-- `log k ≤ 2 * √k` for `0 < k`, via `log k = 2 log √k ≤ 2 (√k - 1)`. -/
private theorem chapter8_log_le_two_sqrt {k : ℝ} (hk : 0 < k) :
    Real.log k ≤ 2 * Real.sqrt k := by
  have hs_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hk_eq : k = Real.sqrt k ^ 2 := (Real.sq_sqrt hk.le).symm
  have hlog_s : Real.log (Real.sqrt k) ≤ Real.sqrt k - 1 :=
    Real.log_le_sub_one_of_pos hs_pos
  have hlog_s_le : Real.log (Real.sqrt k) ≤ Real.sqrt k := by linarith
  calc Real.log k = Real.log (Real.sqrt k ^ 2) := by conv_lhs => rw [hk_eq]
    _ = 2 * Real.log (Real.sqrt k) := by
      rw [Real.log_pow]
      norm_num
    _ ≤ 2 * Real.sqrt k := by linarith

/-- `√k / k^2 = (k ^ (3/2))⁻¹` for `0 < k`. -/
private theorem chapter8_sqrt_div_sq_eq {k : ℝ} (hk : 0 < k) :
    Real.sqrt k / k ^ 2 = (k ^ (3 / 2 : ℝ))⁻¹ := by
  have hk_le : (0 : ℝ) ≤ k := le_of_lt hk
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two k, ← Real.rpow_sub hk]
  have hexp : (1 / 2 : ℝ) - 2 = -(3 / 2 : ℝ) := by norm_num
  rw [hexp, Real.rpow_neg hk_le]

/-- `1 / k^2 ≤ (k ^ (3/2))⁻¹` for `1 ≤ k`. -/
private theorem chapter8_one_div_sq_le {k : ℝ} (hk1 : 1 ≤ k) :
    1 / k ^ 2 ≤ (k ^ (3 / 2 : ℝ))⁻¹ := by
  have hk : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hk1
  have hpow_pos : (0 : ℝ) < k ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hk _
  have hpow2_pos : (0 : ℝ) < k ^ (2 : ℝ) := Real.rpow_pos_of_pos hk _
  have hle : k ^ (3 / 2 : ℝ) ≤ k ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  have heq : (1 : ℝ) / k ^ 2 = (k ^ (2 : ℝ))⁻¹ := by
    rw [one_div, ← Real.rpow_two k]
  rw [heq]
  exact (inv_le_inv₀ hpow2_pos hpow_pos).mpr hle

/-- Shifted `p`-series at `p = 3/2` over `j + 1`. -/
private theorem chapter8_shifted_rpow_summable :
    Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) 1).mpr
    hbase

/-- Algebraic split of the Entry 17 term:
`log k / k - log (k+y) / (k+y) = log k * y / (k*(k+y)) - log(1+y/k)/(k+y)`. -/
private theorem chapter8_term_split (y : ℝ) (j : ℕ)
    (hk_pos : (0 : ℝ) < (j : ℝ) + 1)
    (hky_pos : (0 : ℝ) < ((j : ℝ) + 1) + y)
    (h1yk_pos : (0 : ℝ) < 1 + y / ((j : ℝ) + 1)) :
    chapter8Entry17Term y j =
      Real.log ((j : ℝ) + 1) * y / (((j : ℝ) + 1) * (((j : ℝ) + 1) + y)) -
      Real.log (1 + y / ((j : ℝ) + 1)) / (((j : ℝ) + 1) + y) := by
  have hk_ne : ((j : ℝ) + 1) ≠ 0 := ne_of_gt hk_pos
  have hky_ne : (((j : ℝ) + 1) + y) ≠ 0 := ne_of_gt hky_pos
  have h1yk_ne : (1 + y / ((j : ℝ) + 1)) ≠ 0 := ne_of_gt h1yk_pos
  have hterm_eq : chapter8Entry17Term y j =
      Real.log ((j : ℝ) + 1) / ((j : ℝ) + 1) -
      Real.log (((j : ℝ) + 1) + y) / (((j : ℝ) + 1) + y) := rfl
  have hky_eq : ((j : ℝ) + 1) + y = ((j : ℝ) + 1) * (1 + y / ((j : ℝ) + 1)) := by
    field_simp
  have hlog_split : Real.log (((j : ℝ) + 1) + y) =
      Real.log ((j : ℝ) + 1) + Real.log (1 + y / ((j : ℝ) + 1)) := by
    conv_lhs => rw [hky_eq]
    rw [Real.log_mul hk_ne h1yk_ne]
  rw [hterm_eq, hlog_split]
  field_simp
  ring

/-- Bound for the first part `|log k * y / (k*(k+y))| ≤ 4*|y|*(k^(3/2))⁻¹`. -/
private theorem chapter8_first_bound (y : ℝ) (j : ℕ)
    (hj : 2 * |y| ≤ (j : ℝ) + 1) :
    |Real.log ((j : ℝ) + 1) * y / (((j : ℝ) + 1) * (((j : ℝ) + 1) + y))| ≤
      4 * |y| * ((((j : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hk1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith
  have hk_pos : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hk_ne : ((j : ℝ) + 1) ≠ 0 := ne_of_gt hk_pos
  have hky_ge : ((j : ℝ) + 1) / 2 ≤ ((j : ℝ) + 1) + y := by
    have h1 : |y| ≤ ((j : ℝ) + 1) / 2 := by linarith
    have h2 : -|y| ≤ y := neg_abs_le y
    linarith
  have hky_pos : (0 : ℝ) < ((j : ℝ) + 1) + y := by
    have hhalf : (0 : ℝ) < ((j : ℝ) + 1) / 2 := by linarith
    linarith
  have hden_pos : (0 : ℝ) < ((j : ℝ) + 1) * (((j : ℝ) + 1) + y) :=
    mul_pos hk_pos hky_pos
  have hlog_nonneg : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg hk1
  have hlog_le : Real.log ((j : ℝ) + 1) ≤ 2 * Real.sqrt ((j : ℝ) + 1) :=
    chapter8_log_le_two_sqrt hk_pos
  have hfirst_eq :
      |Real.log ((j : ℝ) + 1) * y / (((j : ℝ) + 1) * (((j : ℝ) + 1) + y))| =
      Real.log ((j : ℝ) + 1) * |y| / (((j : ℝ) + 1) * (((j : ℝ) + 1) + y)) := by
    rw [abs_div, abs_mul, abs_of_nonneg hlog_nonneg, abs_of_pos hden_pos]
  have hsq_pos : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := pow_pos hk_pos 2
  have hk2_pos : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 / 2 := by linarith
  have hden_ge : ((j : ℝ) + 1) ^ 2 / 2 ≤ ((j : ℝ) + 1) * (((j : ℝ) + 1) + y) := by
    have h := mul_le_mul_of_nonneg_left hky_ge (le_of_lt hk_pos)
    have heq : ((j : ℝ) + 1) * (((j : ℝ) + 1) / 2) = ((j : ℝ) + 1) ^ 2 / 2 := by
      ring
    rw [← heq]
    exact h
  have hnum_le : Real.log ((j : ℝ) + 1) * |y| ≤
      (2 * Real.sqrt ((j : ℝ) + 1)) * |y| :=
    mul_le_mul_of_nonneg_right hlog_le (abs_nonneg y)
  have hnum2_nonneg : (0 : ℝ) ≤ (2 * Real.sqrt ((j : ℝ) + 1)) * |y| :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (abs_nonneg y)
  have hle : Real.log ((j : ℝ) + 1) * |y| /
      (((j : ℝ) + 1) * (((j : ℝ) + 1) + y)) ≤
      ((2 * Real.sqrt ((j : ℝ) + 1)) * |y|) / (((j : ℝ) + 1) ^ 2 / 2) :=
    div_le_div₀ hnum2_nonneg hnum_le hk2_pos hden_ge
  have hk2_ne : ((j : ℝ) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hk_ne
  have hsqrt_eq := chapter8_sqrt_div_sq_eq hk_pos
  have heq : ((2 * Real.sqrt ((j : ℝ) + 1)) * |y|) / (((j : ℝ) + 1) ^ 2 / 2) =
      4 * |y| * ((((j : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    rw [← hsqrt_eq]
    field_simp
    ring
  rw [hfirst_eq]
  linarith [hle, heq]

/-- Bound for the second part `|log(1+y/k)/(k+y)| ≤ 4*|y|*(k^(3/2))⁻¹`. -/
private theorem chapter8_second_bound (y : ℝ) (j : ℕ)
    (hj : 2 * |y| ≤ (j : ℝ) + 1) :
    |Real.log (1 + y / ((j : ℝ) + 1)) / (((j : ℝ) + 1) + y)| ≤
      4 * |y| * ((((j : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hk1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith
  have hk_pos : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hk_ne : ((j : ℝ) + 1) ≠ 0 := ne_of_gt hk_pos
  have hky_ge : ((j : ℝ) + 1) / 2 ≤ ((j : ℝ) + 1) + y := by
    have h1 : |y| ≤ ((j : ℝ) + 1) / 2 := by linarith
    have h2 : -|y| ≤ y := neg_abs_le y
    linarith
  have hky_pos : (0 : ℝ) < ((j : ℝ) + 1) + y := by
    have hhalf : (0 : ℝ) < ((j : ℝ) + 1) / 2 := by linarith
    linarith
  have hk_half_pos : (0 : ℝ) < ((j : ℝ) + 1) / 2 := by linarith
  have ht_abs : |y / ((j : ℝ) + 1)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hk_pos, div_le_iff₀ hk_pos]
    linarith
  have h1yk_eq : 1 + y / ((j : ℝ) + 1) = (((j : ℝ) + 1) + y) / ((j : ℝ) + 1) := by
    field_simp
  have h1yk_pos : (0 : ℝ) < 1 + y / ((j : ℝ) + 1) := by
    rw [h1yk_eq]
    exact div_pos hky_pos hk_pos
  have hlog_bound : |Real.log (1 + y / ((j : ℝ) + 1))| ≤
      2 * |y / ((j : ℝ) + 1)| :=
    chapter8_log_one_add_bound ht_abs h1yk_pos
  have htyk_eq : |y / ((j : ℝ) + 1)| = |y| / ((j : ℝ) + 1) := by
    rw [abs_div, abs_of_pos hk_pos]
  have hnum_le2 : |Real.log (1 + y / ((j : ℝ) + 1))| ≤
      2 * (|y| / ((j : ℝ) + 1)) := by
    linarith [hlog_bound, htyk_eq]
  have hnum2_nonneg : (0 : ℝ) ≤ 2 * (|y| / ((j : ℝ) + 1)) :=
    mul_nonneg (by norm_num) (div_nonneg (abs_nonneg y) (le_of_lt hk_pos))
  have hsecond_eq :
      |Real.log (1 + y / ((j : ℝ) + 1)) / (((j : ℝ) + 1) + y)| =
      |Real.log (1 + y / ((j : ℝ) + 1))| / (((j : ℝ) + 1) + y) := by
    rw [abs_div, abs_of_pos hky_pos]
  have hle : |Real.log (1 + y / ((j : ℝ) + 1))| / (((j : ℝ) + 1) + y) ≤
      (2 * (|y| / ((j : ℝ) + 1))) / (((j : ℝ) + 1) / 2) :=
    div_le_div₀ hnum2_nonneg hnum_le2 hk_half_pos hky_ge
  have heq2 : (2 * (|y| / ((j : ℝ) + 1))) / (((j : ℝ) + 1) / 2) =
      (4 * |y|) * (1 / ((j : ℝ) + 1) ^ 2) := by
    field_simp
    ring
  have h4Y_nonneg : (0 : ℝ) ≤ 4 * |y| :=
    mul_nonneg (by norm_num) (abs_nonneg y)
  have hone_le := chapter8_one_div_sq_le hk1
  have hle2 : (4 * |y|) * (1 / ((j : ℝ) + 1) ^ 2) ≤
      (4 * |y|) * ((((j : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) :=
    mul_le_mul_of_nonneg_left hone_le h4Y_nonneg
  rw [hsecond_eq]
  linarith [hle, heq2, hle2]

/-- Combined eventual pointwise bound for the Entry 17 term. -/
private theorem chapter8_term_bound (y : ℝ) (j : ℕ)
    (hj : 2 * |y| ≤ (j : ℝ) + 1) :
    |chapter8Entry17Term y j| ≤ 8 * |y| * ((((j : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hk_pos : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hky_ge : ((j : ℝ) + 1) / 2 ≤ ((j : ℝ) + 1) + y := by
    have h1 : |y| ≤ ((j : ℝ) + 1) / 2 := by linarith
    have h2 : -|y| ≤ y := neg_abs_le y
    linarith
  have hky_pos : (0 : ℝ) < ((j : ℝ) + 1) + y := by
    have hhalf : (0 : ℝ) < ((j : ℝ) + 1) / 2 := by linarith
    linarith
  have h1yk_eq : 1 + y / ((j : ℝ) + 1) = (((j : ℝ) + 1) + y) / ((j : ℝ) + 1) := by
    have hk_ne : ((j : ℝ) + 1) ≠ 0 := ne_of_gt hk_pos
    field_simp
  have h1yk_pos : (0 : ℝ) < 1 + y / ((j : ℝ) + 1) := by
    rw [h1yk_eq]
    exact div_pos hky_pos hk_pos
  have hsplit := chapter8_term_split y j hk_pos hky_pos h1yk_pos
  have hfirst := chapter8_first_bound y j hj
  have hsecond := chapter8_second_bound y j hj
  rw [hsplit]
  calc |Real.log ((j : ℝ) + 1) * y / (((j : ℝ) + 1) * (((j : ℝ) + 1) + y)) -
        Real.log (1 + y / ((j : ℝ) + 1)) / (((j : ℝ) + 1) + y)|
        ≤ |Real.log ((j : ℝ) + 1) * y / (((j : ℝ) + 1) * (((j : ℝ) + 1) + y))| +
          |Real.log (1 + y / ((j : ℝ) + 1)) / (((j : ℝ) + 1) + y)| :=
        abs_sub _ _
    _ ≤ 4 * |y| * ((((j : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) +
          (4 * |y| * ((((j : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹)) :=
        add_le_add hfirst hsecond
    _ = 8 * |y| * ((((j : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by ring

/-- Pointwise identity for one layer: `g(N+1+(x-k)/n)` equals the
corresponding `n * h - n log n / (m+x)` term with `m = n*N+(n-1-k)+1`. -/
private theorem chapter8_pointwise_identity (x : ℝ) (n N k : ℕ)
    (hx : -1 < x) (hn : 0 < n) (hk : k < n) :
    Real.log (((N : ℝ) + 1) + (x - k) / n) / (((N : ℝ) + 1) + (x - k) / n) =
      (n : ℝ) * (Real.log (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) /
        (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x)) -
      (n : ℝ) * Real.log n / (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have h1n : 1 ≤ n := by omega
  have hkn : k ≤ n - 1 := by omega
  have hcast_r : (((n - 1 - k : ℕ)) : ℝ) = (n : ℝ) - 1 - (k : ℝ) := by
    rw [Nat.cast_sub hkn, Nat.cast_sub h1n, Nat.cast_one]
  have hcast_i : ((((n * N + (n - 1 - k) : ℕ))) : ℝ) =
      (n : ℝ) * (N : ℝ) + (((n - 1 - k : ℕ)) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_mul]
  have hm_eq : (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) : ℝ) =
      (n : ℝ) * ((N : ℝ) + 1) - (k : ℝ) := by
    rw [hcast_i, hcast_r]
    ring
  have h1 : ((N : ℝ) + 1) + (x - (k : ℝ)) / (n : ℝ) =
      ((((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x)) / (n : ℝ) := by
    rw [hm_eq]
    field_simp
    ring
  have hi0 : (0 : ℝ) ≤ ((((n * N + (n - 1 - k) : ℕ))) : ℝ) := Nat.cast_nonneg _
  have hm_pos : (0 : ℝ) < (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) := by
    linarith
  have hm_ne : (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) ≠ 0 :=
    ne_of_gt hm_pos
  have hlog_div : Real.log ((((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) / (n : ℝ)) =
      Real.log (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) - Real.log (n : ℝ) :=
    Real.log_div hm_ne hnR_ne
  have hg_eq : Real.log (((N : ℝ) + 1) + (x - (k : ℝ)) / (n : ℝ)) /
      (((N : ℝ) + 1) + (x - (k : ℝ)) / (n : ℝ)) =
      (n : ℝ) * (Real.log (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) -
        Real.log (n : ℝ)) / (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) := by
    rw [h1, hlog_div]
    field_simp
  rw [hg_eq]
  ring

/-- One-layer sum identity: summing the pointwise identity over `k < n`
gives the `Ico` sums. -/
private theorem chapter8_layer_identity (x : ℝ) (n N : ℕ) (hx : -1 < x) (hn : 0 < n) :
    ∑ k ∈ Finset.range n,
        (Real.log (((N : ℝ) + 1) + (x - k) / n) / (((N : ℝ) + 1) + (x - k) / n)) =
      (n : ℝ) * (∑ i ∈ Finset.Ico (n * N) (n * (N + 1)),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
      (n : ℝ) * Real.log n *
        (∑ i ∈ Finset.Ico (n * N) (n * (N + 1)), 1 / (((i : ℝ) + 1) + x)) := by
  have hN : n * (N + 1) = n * N + n := Nat.mul_succ n N
  have hsub : n * N + n - n * N = n := by omega
  have hIco_h : ∑ i ∈ Finset.Ico (n * N) (n * (N + 1)),
      Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x) =
      ∑ k ∈ Finset.range n,
        Real.log (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) /
          (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) := by
    rw [hN, Finset.sum_Ico_eq_sum_range, hsub]
    exact (Finset.sum_range_reflect
      (fun r => Real.log (((((n * N + r : ℕ)) : ℝ) + 1) + x) /
        (((((n * N + r : ℕ)) : ℝ) + 1) + x)) n).symm
  have hIco_u : ∑ i ∈ Finset.Ico (n * N) (n * (N + 1)), 1 / (((i : ℝ) + 1) + x) =
      ∑ k ∈ Finset.range n, 1 / (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) := by
    rw [hN, Finset.sum_Ico_eq_sum_range, hsub]
    exact (Finset.sum_range_reflect
      (fun r => 1 / (((((n * N + r : ℕ)) : ℝ) + 1) + x)) n).symm
  have hpoint : ∀ k ∈ Finset.range n,
      Real.log (((N : ℝ) + 1) + (x - k) / n) / (((N : ℝ) + 1) + (x - k) / n) =
        (n : ℝ) * (Real.log (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) /
          (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x)) -
        (n : ℝ) * Real.log n / (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact chapter8_pointwise_identity x n N k hx hn hk
  have hsum_point : ∑ k ∈ Finset.range n,
      (Real.log (((N : ℝ) + 1) + (x - k) / n) / (((N : ℝ) + 1) + (x - k) / n)) =
      ∑ k ∈ Finset.range n,
        ((n : ℝ) * (Real.log (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x) /
          (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x)) -
        (n : ℝ) * Real.log n / (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x)) :=
    Finset.sum_congr rfl hpoint
  have hsecond_eq : (∑ k ∈ Finset.range n,
        (n : ℝ) * Real.log n / (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x)) =
      ((n : ℝ) * Real.log n) *
        (∑ k ∈ Finset.range n, 1 / (((((n * N + (n - 1 - k) : ℕ)) : ℝ) + 1) + x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [div_eq_mul_one_div]
  rw [hsum_point, Finset.sum_sub_distrib, ← Finset.mul_sum, hsecond_eq,
    ← hIco_h, ← hIco_u]

/-- Increment identity: the `N`-th layer of the truncated identity. -/
private theorem chapter8_increment_identity (x : ℝ) (n N : ℕ) (hx : -1 < x) (hn : 0 < n) :
    (n : ℝ) * (chapter8Entry17Term x N) -
        ∑ k ∈ Finset.range n, chapter8Entry17Term ((x - k) / n) N =
      (n : ℝ) * ((∑ i ∈ Finset.Ico (n * N) (n * (N + 1)),
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
        Real.log (((N : ℝ) + 1) + x) / (((N : ℝ) + 1) + x)) -
      (n : ℝ) * Real.log n *
        (∑ i ∈ Finset.Ico (n * N) (n * (N + 1)), 1 / (((i : ℝ) + 1) + x)) := by
  have hterm_x : chapter8Entry17Term x N =
      Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1) -
      Real.log (((N : ℝ) + 1) + x) / (((N : ℝ) + 1) + x) := rfl
  have hterm_y : ∀ k : ℕ, chapter8Entry17Term ((x - k) / n) N =
      Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1) -
      Real.log (((N : ℝ) + 1) + (x - k) / n) / (((N : ℝ) + 1) + (x - k) / n) :=
    fun k => rfl
  have hincL_eq : (n : ℝ) * (chapter8Entry17Term x N) -
      ∑ k ∈ Finset.range n, chapter8Entry17Term ((x - k) / n) N =
      (∑ k ∈ Finset.range n,
        Real.log (((N : ℝ) + 1) + (x - k) / n) / (((N : ℝ) + 1) + (x - k) / n)) -
      (n : ℝ) * (Real.log (((N : ℝ) + 1) + x) / (((N : ℝ) + 1) + x)) := by
    rw [hterm_x]
    simp only [hterm_y]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hlayer := chapter8_layer_identity x n N hx hn
  rw [hincL_eq, hlayer]
  ring

/-- Truncated identity (Step 1): exact finite-sum version of the goal. -/
private theorem chapter8_truncated_identity (x : ℝ) (n N : ℕ) (hx : -1 < x) (hn : 0 < n) :
    (n : ℝ) * (∑ j ∈ Finset.range N, chapter8Entry17Term x j) -
        ∑ k ∈ Finset.range n, (∑ j ∈ Finset.range N, chapter8Entry17Term ((x - k) / n) j) =
      (n : ℝ) * ((∑ i ∈ Finset.range (n * N),
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
        (∑ i ∈ Finset.range N,
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
      (n : ℝ) * Real.log n *
        (∑ i ∈ Finset.range (n * N), 1 / (((i : ℝ) + 1) + x)) := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    have hle : n * N ≤ n * (N + 1) := by
      rw [Nat.mul_succ]
      exact Nat.le_add_right _ _
    have hH1 : ∑ i ∈ Finset.range (n * (N + 1)),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x) =
        (∑ i ∈ Finset.range (n * N),
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) +
        (∑ i ∈ Finset.Ico (n * N) (n * (N + 1)),
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) :=
      (sum_range_add_sum_Ico _ hle).symm
    have hH3 : ∑ i ∈ Finset.range (n * (N + 1)), 1 / (((i : ℝ) + 1) + x) =
        (∑ i ∈ Finset.range (n * N), 1 / (((i : ℝ) + 1) + x)) +
        (∑ i ∈ Finset.Ico (n * N) (n * (N + 1)), 1 / (((i : ℝ) + 1) + x)) :=
      (sum_range_add_sum_Ico _ hle).symm
    have hinc := chapter8_increment_identity x n N hx hn
    simp only [Finset.sum_range_succ, hH1, hH3, Finset.sum_add_distrib] at ⊢ ih hinc
    linear_combination ih + hinc

/-- (Step 3a) `log ∘ Gamma` has derivative `psi y` at `y > 0`. -/
private theorem chapter8_hasDerivAt_logGamma {y : ℝ} (hy : 0 < y) :
    HasDerivAt (Real.log ∘ Real.Gamma) (chapter8RealDigamma y) y := by
  have hdiff : DifferentiableAt ℝ Real.Gamma y :=
    Real.differentiableAt_Gamma (fun m => by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hlt : -((m : ℝ)) < y := by linarith
      exact ne_of_gt hlt)
  have hne : Real.Gamma y ≠ 0 := (Real.Gamma_pos_of_pos hy).ne'
  exact hdiff.hasDerivAt.log hne

/-- (Step 3b) Digamma recurrence `psi (y+1) = psi y + 1/y` for `y > 0`. -/
private theorem chapter8_digamma_add_one {y : ℝ} (hy : 0 < y) :
    chapter8RealDigamma (y + 1) = chapter8RealDigamma y + 1 / y := by
  have hy_ne : y ≠ 0 := ne_of_gt hy
  have hdiff_y : DifferentiableAt ℝ Real.Gamma y :=
    Real.differentiableAt_Gamma (fun m => by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hlt : -((m : ℝ)) < y := by linarith
      exact ne_of_gt hlt)
  have hy1_pos : (0 : ℝ) < y + 1 := by linarith
  have hdiff_y1 : DifferentiableAt ℝ Real.Gamma (y + 1) :=
    Real.differentiableAt_Gamma (fun m => by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hlt : -((m : ℝ)) < y + 1 := by linarith
      exact ne_of_gt hlt)
  have h_left : HasDerivAt (fun s => Real.Gamma (s + 1)) (deriv Real.Gamma (y + 1)) y :=
    HasDerivAt.comp_add_const y 1 hdiff_y1.hasDerivAt
  have h_right : HasDerivAt (fun s => s * Real.Gamma s)
      (1 * Real.Gamma y + y * deriv Real.Gamma y) y :=
    (hasDerivAt_id' y).mul hdiff_y.hasDerivAt
  have heq : (fun s => Real.Gamma (s + 1)) =ᶠ[𝓝 y] (fun s => s * Real.Gamma s) := by
    filter_upwards [eventually_ne_nhds hy_ne] with s hs using Real.Gamma_add_one hs
  have h_left' : HasDerivAt (fun s => s * Real.Gamma s) (deriv Real.Gamma (y + 1)) y :=
    h_left.congr_of_eventuallyEq heq.symm
  have hder_eq : deriv Real.Gamma (y + 1) =
      1 * Real.Gamma y + y * deriv Real.Gamma y :=
    HasDerivAt.unique h_left' h_right
  have hG_y_pos : (0 : ℝ) < Real.Gamma y := Real.Gamma_pos_of_pos hy
  have hG_y_ne : Real.Gamma y ≠ 0 := ne_of_gt hG_y_pos
  have hG_y1_eq : Real.Gamma (y + 1) = y * Real.Gamma y :=
    Real.Gamma_add_one hy_ne
  have hG_y1_ne : Real.Gamma (y + 1) ≠ 0 := by
    rw [hG_y1_eq]
    exact mul_ne_zero hy_ne hG_y_ne
  unfold chapter8RealDigamma
  rw [hder_eq, hG_y1_eq]
  field_simp
  ring

/-- (Step 3c) `log y ≤ psi (y+1) ≤ log (y+1)` for `y > 0`, from convexity. -/
private theorem chapter8_digamma_bounds {y : ℝ} (hy : 0 < y) :
    Real.log y ≤ chapter8RealDigamma (y + 1) ∧
      chapter8RealDigamma (y + 1) ≤ Real.log (y + 1) := by
  have hy1_pos : (0 : ℝ) < y + 1 := by linarith
  have hy2_pos : (0 : ℝ) < (y + 1) + 1 := by linarith
  have hx_mem : y ∈ Set.Ioi (0 : ℝ) := hy
  have hy1_mem : y + 1 ∈ Set.Ioi (0 : ℝ) := hy1_pos
  have hy2_mem : (y + 1) + 1 ∈ Set.Ioi (0 : ℝ) := hy2_pos
  have hxy1 : y < y + 1 := by linarith
  have hxy2 : y + 1 < (y + 1) + 1 := by linarith
  have hderiv_y1 := chapter8_hasDerivAt_logGamma hy1_pos
  have hle1 := Real.convexOn_log_Gamma.slope_le_of_hasDerivAt hx_mem hy1_mem hxy1
    hderiv_y1
  have hle2 := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt hy1_mem hy2_mem hxy2
    hderiv_y1
  have hslope1 : slope (Real.log ∘ Real.Gamma) y (y + 1) = Real.log y := by
    rw [slope_def_field]
    have hden : (y + 1) - y = 1 := by ring
    rw [hden, div_one]
    have hG : Real.Gamma (y + 1) = y * Real.Gamma y :=
      Real.Gamma_add_one (ne_of_gt hy)
    have hlog : Real.log (y * Real.Gamma y) =
        Real.log y + Real.log (Real.Gamma y) :=
      Real.log_mul (ne_of_gt hy) (ne_of_gt (Real.Gamma_pos_of_pos hy))
    simp only [Function.comp_apply]
    rw [hG, hlog]
    ring
  have hslope2 : slope (Real.log ∘ Real.Gamma) (y + 1) ((y + 1) + 1) =
      Real.log (y + 1) := by
    rw [slope_def_field]
    have hden : ((y + 1) + 1) - (y + 1) = 1 := by ring
    rw [hden, div_one]
    have hG : Real.Gamma ((y + 1) + 1) = (y + 1) * Real.Gamma (y + 1) :=
      Real.Gamma_add_one (ne_of_gt hy1_pos)
    have hlog : Real.log ((y + 1) * Real.Gamma (y + 1)) =
        Real.log (y + 1) + Real.log (Real.Gamma (y + 1)) :=
      Real.log_mul (ne_of_gt hy1_pos) (ne_of_gt (Real.Gamma_pos_of_pos hy1_pos))
    simp only [Function.comp_apply]
    rw [hG, hlog]
    ring
  rw [hslope1] at hle1
  rw [hslope2] at hle2
  exact ⟨hle1, hle2⟩

/-- Iterated recurrence: `psi (x+1+M) = psi (x+1) + H_M`. -/
private theorem chapter8_digamma_iter (x : ℝ) (hx : -1 < x) (M : ℕ) :
    chapter8RealDigamma ((x + 1) + (M : ℝ)) =
      chapter8RealDigamma (x + 1) +
        ∑ i ∈ Finset.range M, 1 / (((i : ℝ) + 1) + x) := by
  induction M with
  | zero =>
    simp
  | succ M ih =>
    have hy_pos : (0 : ℝ) < (x + 1) + (M : ℝ) := by
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    have hrec := chapter8_digamma_add_one hy_pos
    have heq_arg : (x + 1) + (((M + 1 : ℕ)) : ℝ) = ((x + 1) + (M : ℝ)) + 1 := by
      push_cast
      ring
    have heq_den : (x + 1) + (M : ℝ) = ((M : ℝ) + 1) + x := by ring
    rw [heq_arg, Finset.sum_range_succ, ← heq_den]
    linear_combination ih + hrec

/-- Harmonic limit: `H_M - log (x+M) → -psi (x+1)`. -/
private theorem chapter8_harmonic_limit (x : ℝ) (hx : -1 < x) :
    Tendsto (fun M : ℕ => (∑ i ∈ Finset.range M, 1 / (((i : ℝ) + 1) + x)) -
      Real.log ((M : ℝ) + x)) atTop (𝓝 (-chapter8RealDigamma (x + 1))) := by
  have hU : Tendsto (fun M : ℕ => Real.log ((((M : ℝ) + x) + 1)) -
      Real.log ((M : ℝ) + x)) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log 1).comp
      (tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop)
  have hpsi0 : Tendsto (fun M : ℕ => chapter8RealDigamma ((x + 1) + (M : ℝ)) -
      Real.log ((M : ℝ) + x)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with M hM
      have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hy_pos : (0 : ℝ) < (M : ℝ) + x := by linarith
      have harg_eq : ((M : ℝ) + x) + 1 = (x + 1) + (M : ℝ) := by ring
      have hbounds := chapter8_digamma_bounds hy_pos
      rw [← harg_eq]
      linarith [hbounds.1]
    · filter_upwards [eventually_ge_atTop 1] with M hM
      have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hy_pos : (0 : ℝ) < (M : ℝ) + x := by linarith
      have harg_eq : ((M : ℝ) + x) + 1 = (x + 1) + (M : ℝ) := by ring
      have hbounds := chapter8_digamma_bounds hy_pos
      rw [← harg_eq]
      linarith [hbounds.2]
  have hfun_eq : ∀ M : ℕ, (∑ i ∈ Finset.range M, 1 / (((i : ℝ) + 1) + x)) -
      Real.log ((M : ℝ) + x) =
      (chapter8RealDigamma ((x + 1) + (M : ℝ)) - Real.log ((M : ℝ) + x)) -
        chapter8RealDigamma (x + 1) := by
    intro M
    have hiterM := chapter8_digamma_iter x hx M
    linarith
  have hlim : Tendsto (fun M : ℕ =>
      (chapter8RealDigamma ((x + 1) + (M : ℝ)) - Real.log ((M : ℝ) + x)) -
        chapter8RealDigamma (x + 1)) atTop (𝓝 (-chapter8RealDigamma (x + 1))) := by
    have h := hpsi0.sub_const (chapter8RealDigamma (x + 1))
    simpa using h
  exact hlim.congr' (Eventually.of_forall (fun M => (hfun_eq M).symm))

private theorem chapter8_aux_summable (y : ℝ) (_hy : -1 < y) :
    Summable (chapter8Entry17Term y) := by
  have hsumC : Summable (fun j : ℕ => (8 * |y|) * ((((j + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹)) :=
    chapter8_shifted_rpow_summable.mul_left (8 * |y|)
  have hcast : ∀ j : ℕ, (((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1) := fun j => by
    push_cast
    ring
  have hsumC' : Summable (fun j : ℕ => (8 * |y|) * ((((j : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹)) := by
    simp only [← hcast]
    exact hsumC
  refine Summable.of_norm_bounded_eventually_nat hsumC' ?_
  obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * |y|)
  filter_upwards [eventually_ge_atTop N0] with j hj
  have hjR : (N0 : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hj
  have hj_thresh : 2 * |y| ≤ (j : ℝ) + 1 := by linarith
  have hbound := chapter8_term_bound y j hj_thresh
  rw [Real.norm_eq_abs]
  exact hbound

/-- Derivative of `(log t)^2 / 2` is `log t / t`. -/
private theorem chapter8_log_sq_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (Real.log t) ^ 2 / 2) (Real.log t / t) t := by
  have hx : t ≠ 0 := ne_of_gt ht
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log hx
  have hsq : HasDerivAt (Real.log ^ 2) ((2 : ℝ) * Real.log t ^ (2 - 1) * t⁻¹) t :=
    hlog.pow 2
  have hdiv : HasDerivAt (fun u : ℝ => (Real.log ^ 2) u / 2)
      (((2 : ℝ) * Real.log t ^ (2 - 1) * t⁻¹) / 2) t :=
    hsq.div_const 2
  have hfun_eq : (fun u : ℝ => (Real.log ^ 2) u / 2) =
      (fun t : ℝ => (Real.log t) ^ 2 / 2) := by
    simp only [Pi.pow_apply]
  have hderiv_eq : ((2 : ℝ) * Real.log t ^ (2 - 1) * t⁻¹) / 2 =
      Real.log t / t := by
    field_simp
    ring
  rw [hfun_eq, hderiv_eq] at hdiv
  exact hdiv

/-- Integral of `log t / t` is `(log b)^2/2 - (log a)^2/2`. -/
private theorem chapter8_log_div_integral {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    (∫ t in a..b, Real.log t / t) =
      (Real.log b) ^ 2 / 2 - (Real.log a) ^ 2 / 2 := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => (Real.log t) ^ 2 / 2)
        (Real.log x / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    exact chapter8_log_sq_hasDerivAt hx_pos
  have hcont : ContinuousOn (fun t : ℝ => Real.log t / t)
      (Set.uIcc a b) := by
    have hsub : Set.uIcc a b ⊆ {0}ᶜ := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx_pos
    have hlog : ContinuousOn Real.log (Set.uIcc a b) :=
      Real.continuousOn_log.mono hsub
    have hid : ContinuousOn id (Set.uIcc a b) := continuousOn_id
    have hne : ∀ x ∈ Set.uIcc a b, id x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
      simp only [id_eq]
      exact ne_of_gt hx_pos
    have h := hlog.div hid hne
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => Real.log t / t)
      MeasureTheory.volume a b :=
    hcont.intervalIntegrable
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa only using heq

/-- `exp 1 < 3`, so `[3, ∞)` lies in the antitone region of `log x / x`. -/
private theorem chapter8_exp_one_lt_three : Real.exp 1 < 3 := by
  have h := Real.exp_one_lt_d9
  linarith

/-- `log x / x` is antitone on `[a, b]` when `3 ≤ a`. -/
private theorem chapter8_antitone_Icc {a b : ℝ} (ha : 3 ≤ a)
    (_hab : a ≤ b) :
    AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Icc a b) := by
  apply Real.log_div_self_antitoneOn.mono
  intro x hx
  simp only [Set.mem_Ici, Set.mem_Icc] at hx ⊢
  have hexp := chapter8_exp_one_lt_three
  linarith [hx.1]

/-- `log t / t → 0` as `t → ∞`. -/
private theorem chapter8_log_div_tendsto_zero :
    Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have heq : (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) =
      (fun t : ℝ => Real.log t / t) := by
    simp only [pow_one, one_mul, add_zero]
  rw [heq] at h
  exact h

/-- `N + 1 + x → ∞` as `N → ∞`. -/
private theorem chapter8_A_tendsto_atTop (x : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) + 1 + x) atTop atTop := by
  have hbase : Tendsto (fun N : ℕ => (N : ℝ) + (1 + x)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 + x)
      tendsto_natCast_atTop_atTop
  apply hbase.congr' _
  filter_upwards with N
  ring

/-- `n * N + 1 + x → ∞` as `N → ∞` for `0 < n`. -/
private theorem chapter8_B_tendsto_atTop (x : ℝ) (n : ℕ)
    (hn : 0 < n) :
    Tendsto (fun N : ℕ => ((n * N : ℕ) : ℝ) + 1 + x) atTop atTop := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmul : Tendsto (fun N : ℕ => (n : ℝ) * (N : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hnR tendsto_natCast_atTop_atTop
  have hadd : Tendsto (fun N : ℕ => (n : ℝ) * (N : ℝ) + (1 + x))
      atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 + x) hmul
  apply hadd.congr' _
  filter_upwards with N
  push_cast
  ring

/-- Partial sums converge to `Phi`. -/
private theorem chapter8_partial_tendsto (y : ℝ)
    (h : Summable (chapter8Entry17Term y)) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, chapter8Entry17Term y j)
      atTop (𝓝 (chapter8Entry17Phi y)) := by
  have h' := h.hasSum.tendsto_sum_nat
  simpa [chapter8Entry17Phi] using h'

/-- Left side of the truncated identity converges to the goal left side. -/
private theorem chapter8_LHS_tendsto (x : ℝ) (n : ℕ)
    (h3 : Summable (chapter8Entry17Term x))
    (h4 : ∀ k ∈ Finset.range n, Summable (chapter8Entry17Term ((x - k) / n))) :
    Tendsto (fun N : ℕ => (n : ℝ) *
        (∑ j ∈ Finset.range N, chapter8Entry17Term x j) -
        ∑ k ∈ Finset.range n,
          (∑ j ∈ Finset.range N, chapter8Entry17Term ((x - k) / n) j))
      atTop (𝓝 ((n : ℝ) * chapter8Entry17Phi x -
        ∑ k ∈ Finset.range n, chapter8Entry17Phi ((x - k) / n))) := by
  have hx := chapter8_partial_tendsto x h3
  have hmul : Tendsto (fun N : ℕ => (n : ℝ) *
      (∑ j ∈ Finset.range N, chapter8Entry17Term x j))
      atTop (𝓝 ((n : ℝ) * chapter8Entry17Phi x)) :=
    hx.const_mul (n : ℝ)
  have hsum : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range n,
      (∑ j ∈ Finset.range N, chapter8Entry17Term ((x - k) / n) j))
      atTop (𝓝 (∑ k ∈ Finset.range n, chapter8Entry17Phi ((x - k) / n))) :=
    tendsto_finsetSum _ (fun k hk => chapter8_partial_tendsto _ (h4 k hk))
  exact hmul.sub hsum

/-- `N ≤ n * N` for `0 < n`. -/
private theorem chapter8_N_le_nN (n N : ℕ) (hn : 0 < n) : N ≤ n * N :=
  Nat.le_mul_of_pos_left N hn

/-- Telescoping difference of shifted range sums. -/
private theorem chapter8_telescope (g : ℝ → ℝ) (x0 : ℝ) (a : ℕ) :
    (∑ i ∈ Finset.range a, g (x0 + (i : ℝ))) -
      (∑ i ∈ Finset.range a, g (x0 + ((i + 1 : ℕ) : ℝ))) =
      g x0 - g (x0 + (a : ℝ)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linear_combination ih

/-- The `Ico` sum equals the shifted range sum for `g`. -/
private theorem chapter8_S_eq (x : ℝ) (n N : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n * N),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
      (∑ i ∈ Finset.range N,
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) =
      ∑ i ∈ Finset.range (n * N - N),
        Real.log (((N : ℝ) + 1 + x) + (i : ℝ)) /
          (((N : ℝ) + 1 + x) + (i : ℝ)) := by
  have hle := chapter8_N_le_nN n N hn
  have hsum := sum_range_add_sum_Ico
    (fun i : ℕ => Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) hle
  have hdiff : (∑ i ∈ Finset.range (n * N),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
      (∑ i ∈ Finset.range N,
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) =
      ∑ k ∈ Finset.Ico N (n * N),
        Real.log (((k : ℝ) + 1) + x) / (((k : ℝ) + 1) + x) := by
    linear_combination -hsum
  rw [hdiff]
  rw [Finset.sum_Ico_eq_sum_range
    (fun i : ℕ => Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) N (n * N)]
  apply Finset.sum_congr rfl
  intro i _
  have hcast : (((N + i : ℕ)) : ℝ) = (N : ℝ) + (i : ℝ) := Nat.cast_add N i
  have heq : ((((N + i : ℕ)) : ℝ) + 1) + x = ((N : ℝ) + 1 + x) + (i : ℝ) := by
    linear_combination hcast
  rw [heq]

/-- Upper limit identity `x0 + a = x1`. -/
private theorem chapter8_x0_add_a (x : ℝ) (n N : ℕ) (hn : 0 < n) :
    ((N : ℝ) + 1 + x) + ((n * N - N : ℕ) : ℝ) = ((n * N : ℕ) : ℝ) + 1 + x := by
  have hle := chapter8_N_le_nN n N hn
  have hadd : N + (n * N - N) = n * N := Nat.add_sub_cancel' hle
  have hcast : (N : ℝ) + ((n * N - N : ℕ) : ℝ) = ((n * N : ℕ) : ℝ) := by
    rw [← Nat.cast_add, hadd]
  linear_combination hcast

/-- Sandwich bounds `0 ≤ S - I ≤ g x0` for `3 ≤ x0`. -/
private theorem chapter8_sandwich (x : ℝ) (n N : ℕ) (_hn : 0 < n)
    (h3 : 3 ≤ (N : ℝ) + 1 + x) :
    0 ≤ (∑ i ∈ Finset.range (n * N - N),
          Real.log (((N : ℝ) + 1 + x) + (i : ℝ)) /
            (((N : ℝ) + 1 + x) + (i : ℝ))) -
        (∫ t in ((N : ℝ) + 1 + x)..(((N : ℝ) + 1 + x) + ((n * N - N : ℕ) : ℝ)),
          Real.log t / t) ∧
      (∑ i ∈ Finset.range (n * N - N),
          Real.log (((N : ℝ) + 1 + x) + (i : ℝ)) /
            (((N : ℝ) + 1 + x) + (i : ℝ))) -
        (∫ t in ((N : ℝ) + 1 + x)..(((N : ℝ) + 1 + x) + ((n * N - N : ℕ) : ℝ)),
          Real.log t / t) ≤
        Real.log ((N : ℝ) + 1 + x) / ((N : ℝ) + 1 + x) := by
  have ha_nonneg : (0 : ℝ) ≤ ((n * N - N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hab : (N : ℝ) + 1 + x ≤ ((N : ℝ) + 1 + x) + ((n * N - N : ℕ) : ℝ) := by
    linarith
  have h_ant : AntitoneOn (fun x : ℝ => Real.log x / x)
      (Set.Icc ((N : ℝ) + 1 + x)
        (((N : ℝ) + 1 + x) + ((n * N - N : ℕ) : ℝ))) :=
    chapter8_antitone_Icc h3 hab
  have hI_le_S : (∫ t in ((N : ℝ) + 1 + x)..(((N : ℝ) + 1 + x) +
      ((n * N - N : ℕ) : ℝ)), Real.log t / t) ≤
      ∑ i ∈ Finset.range (n * N - N),
        Real.log (((N : ℝ) + 1 + x) + (i : ℝ)) /
          (((N : ℝ) + 1 + x) + (i : ℝ)) :=
    h_ant.integral_le_sum
  have hT_le_I : (∑ i ∈ Finset.range (n * N - N),
        Real.log (((N : ℝ) + 1 + x) + ((i + 1 : ℕ) : ℝ)) /
          (((N : ℝ) + 1 + x) + ((i + 1 : ℕ) : ℝ))) ≤
      (∫ t in ((N : ℝ) + 1 + x)..(((N : ℝ) + 1 + x) +
        ((n * N - N : ℕ) : ℝ)), Real.log t / t) :=
    h_ant.sum_le_integral
  have h_tele := chapter8_telescope (fun x : ℝ => Real.log x / x)
    ((N : ℝ) + 1 + x) (n * N - N)
  have hx1_ge : (3 : ℝ) ≤ ((N : ℝ) + 1 + x) + ((n * N - N : ℕ) : ℝ) := by
    linarith
  have h1_le : (1 : ℝ) ≤ ((N : ℝ) + 1 + x) + ((n * N - N : ℕ) : ℝ) := by
    linarith
  have hlog_nonneg : 0 ≤ Real.log (((N : ℝ) + 1 + x) +
      ((n * N - N : ℕ) : ℝ)) :=
    Real.log_nonneg h1_le
  have hden_pos : (0 : ℝ) < ((N : ℝ) + 1 + x) + ((n * N - N : ℕ) : ℝ) := by
    linarith
  have h_nonneg : (0 : ℝ) ≤ Real.log (((N : ℝ) + 1 + x) +
      ((n * N - N : ℕ) : ℝ)) / (((N : ℝ) + 1 + x) +
      ((n * N - N : ℕ) : ℝ)) :=
    div_nonneg hlog_nonneg (le_of_lt hden_pos)
  constructor
  · linarith [hI_le_S]
  · linarith [hI_le_S, hT_le_I, h_tele, h_nonneg]

/-- `S_N - I_N → 0`. -/
private theorem chapter8_S_sub_I_tendsto (x : ℝ) (n : ℕ) (hn : 0 < n) :
    Tendsto (fun N : ℕ => ((∑ i ∈ Finset.range (n * N),
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
        (∑ i ∈ Finset.range N,
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
        (∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
          Real.log t / t))
      atTop (𝓝 0) := by
  have hS_eq : ∀ N : ℕ, ((∑ i ∈ Finset.range (n * N),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
      (∑ i ∈ Finset.range N,
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) =
      ∑ i ∈ Finset.range (n * N - N),
        Real.log (((N : ℝ) + 1 + x) + (i : ℝ)) /
          (((N : ℝ) + 1 + x) + (i : ℝ)) :=
    fun N => chapter8_S_eq x n N hn
  have hI_eq : ∀ N : ℕ, (∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
        Real.log t / t) =
      (∫ t in ((N : ℝ) + 1 + x)..(((N : ℝ) + 1 + x) + ((n * N - N : ℕ) : ℝ)),
        Real.log t / t) := by
    intro N
    rw [← chapter8_x0_add_a x n N hn]
  have h_eq : (fun N : ℕ => ((∑ i ∈ Finset.range (n * N),
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
        (∑ i ∈ Finset.range N,
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
        (∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
          Real.log t / t)) =ᶠ[atTop]
      (fun N : ℕ => (∑ i ∈ Finset.range (n * N - N),
          Real.log (((N : ℝ) + 1 + x) + (i : ℝ)) /
            (((N : ℝ) + 1 + x) + (i : ℝ))) -
        (∫ t in ((N : ℝ) + 1 + x)..(((N : ℝ) + 1 + x) +
          ((n * N - N : ℕ) : ℝ)), Real.log t / t)) := by
    filter_upwards with N
    rw [hS_eq N, hI_eq N]
  refine Tendsto.congr' h_eq.symm ?_
  have h_lower : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have h_upper : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1 + x) /
      ((N : ℝ) + 1 + x)) atTop (𝓝 0) :=
    chapter8_log_div_tendsto_zero.comp (chapter8_A_tendsto_atTop x)
  have hev3 : ∀ᶠ N : ℕ in atTop, 3 ≤ (N : ℝ) + 1 + x :=
    (chapter8_A_tendsto_atTop x).eventually (eventually_ge_atTop 3)
  have hev_le1 : ∀ᶠ N : ℕ in atTop, (0 : ℝ) ≤
      (∑ i ∈ Finset.range (n * N - N),
        Real.log (((N : ℝ) + 1 + x) + (i : ℝ)) /
          (((N : ℝ) + 1 + x) + (i : ℝ))) -
      (∫ t in ((N : ℝ) + 1 + x)..(((N : ℝ) + 1 + x) +
        ((n * N - N : ℕ) : ℝ)), Real.log t / t) := by
    filter_upwards [hev3] with N hN
    exact (chapter8_sandwich x n N hn hN).1
  have hev_le2 : ∀ᶠ N : ℕ in atTop,
      (∑ i ∈ Finset.range (n * N - N),
        Real.log (((N : ℝ) + 1 + x) + (i : ℝ)) /
          (((N : ℝ) + 1 + x) + (i : ℝ))) -
      (∫ t in ((N : ℝ) + 1 + x)..(((N : ℝ) + 1 + x) +
        ((n * N - N : ℕ) : ℝ)), Real.log t / t) ≤
      Real.log ((N : ℝ) + 1 + x) / ((N : ℝ) + 1 + x) := by
    filter_upwards [hev3] with N hN
    exact (chapter8_sandwich x n N hn hN).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower h_upper
    hev_le1 hev_le2

/-- `x0 > 0` always. -/
private theorem chapter8_x0_pos (x : ℝ) (N : ℕ) (hx : -1 < x) :
    0 < (N : ℝ) + 1 + x := by
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith

/-- `x1 > 0` always. -/
private theorem chapter8_x1_pos (x : ℝ) (n N : ℕ) (hx : -1 < x) :
    0 < ((n * N : ℕ) : ℝ) + 1 + x := by
  have hM : (0 : ℝ) ≤ ((n * N : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- `x0⁻¹ → 0`. -/
private theorem chapter8_inv_x0_tendsto (x : ℝ) :
    Tendsto (fun N : ℕ => (((N : ℝ) + 1 + x))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (chapter8_A_tendsto_atTop x)

/-- `x1 / x0 → n`. -/
private theorem chapter8_ratio_tendsto (x : ℝ) (n : ℕ) (hx : -1 < x)
    (_hn : 0 < n) :
    Tendsto (fun N : ℕ => (((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x))
      atTop (𝓝 (n : ℝ)) := by
  have hC0 : Tendsto (fun N : ℕ => ((1 - (n : ℝ)) * (1 + x)) /
      ((N : ℝ) + 1 + x)) atTop (𝓝 0) := by
    have h_inv := chapter8_inv_x0_tendsto x
    have h_mul : Tendsto (fun N : ℕ => ((1 - (n : ℝ)) * (1 + x)) *
        (((N : ℝ) + 1 + x))⁻¹) atTop (𝓝 (((1 - (n : ℝ)) * (1 + x)) * 0)) :=
      h_inv.const_mul ((1 - (n : ℝ)) * (1 + x))
    simpa [div_eq_mul_inv] using h_mul
  have h_add : Tendsto (fun N : ℕ => (n : ℝ) + ((1 - (n : ℝ)) * (1 + x)) /
      ((N : ℝ) + 1 + x)) atTop (𝓝 ((n : ℝ) + 0)) :=
    tendsto_const_nhds.add hC0
  have h_add0 : Tendsto (fun N : ℕ => (n : ℝ) + ((1 - (n : ℝ)) * (1 + x)) /
      ((N : ℝ) + 1 + x)) atTop (𝓝 (n : ℝ)) := by
    simpa using h_add
  refine Tendsto.congr' ?_ h_add0
  filter_upwards with N
  have hx0_ne : ((N : ℝ) + 1 + x) ≠ 0 :=
    ne_of_gt (chapter8_x0_pos x N hx)
  have hcast : ((n * N : ℕ) : ℝ) = (n : ℝ) * (N : ℝ) := Nat.cast_mul n N
  field_simp
  rw [hcast]
  ring

/-- `D_N = L1 - L2 → log n`. -/
private theorem chapter8_D_tendsto (x : ℝ) (n : ℕ) (hx : -1 < x) (hn : 0 < n) :
    Tendsto (fun N : ℕ => Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      Real.log ((N : ℝ) + 1 + x)) atTop (𝓝 (Real.log (n : ℝ))) := by
  have h_ratio := chapter8_ratio_tendsto x n hx hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have h_log := h_ratio.log hn_ne
  refine Tendsto.congr' ?_ h_log
  filter_upwards with N
  have hx0_ne : ((N : ℝ) + 1 + x) ≠ 0 :=
    ne_of_gt (chapter8_x0_pos x N hx)
  have hx1_ne : (((n * N : ℕ) : ℝ) + 1 + x) ≠ 0 :=
    ne_of_gt (chapter8_x1_pos x n N hx)
  exact Real.log_div hx1_ne hx0_ne

/-- `L1 / x0 → 0`. -/
private theorem chapter8_L1_div_x0_tendsto (x : ℝ) (n : ℕ) (hx : -1 < x)
    (hn : 0 < n) :
    Tendsto (fun N : ℕ => Real.log (((n * N : ℕ) : ℝ) + 1 + x) /
      ((N : ℝ) + 1 + x)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.log (((n * N : ℕ) : ℝ) + 1 + x) /
      (((n * N : ℕ) : ℝ) + 1 + x)) atTop (𝓝 0) :=
    chapter8_log_div_tendsto_zero.comp (chapter8_B_tendsto_atTop x n hn)
  have h2 := chapter8_ratio_tendsto x n hx hn
  have hmul : Tendsto (fun N : ℕ => (Real.log (((n * N : ℕ) : ℝ) + 1 + x) /
      (((n * N : ℕ) : ℝ) + 1 + x)) *
      ((((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)))
      atTop (𝓝 (0 * (n : ℝ))) :=
    h1.mul h2
  have hmul0 : Tendsto (fun N : ℕ => (Real.log (((n * N : ℕ) : ℝ) + 1 + x) /
      (((n * N : ℕ) : ℝ) + 1 + x)) *
      ((((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)))
      atTop (𝓝 0) := by
    simpa using hmul
  refine Tendsto.congr' ?_ hmul0
  filter_upwards with N
  have hx0_ne : ((N : ℝ) + 1 + x) ≠ 0 :=
    ne_of_gt (chapter8_x0_pos x N hx)
  have hx1_ne : (((n * N : ℕ) : ℝ) + 1 + x) ≠ 0 :=
    ne_of_gt (chapter8_x1_pos x n N hx)
  field_simp

/-- `delta_N = log (1 + t_N)` with `t = C / (n * x0)`. -/
private theorem chapter8_delta_eq_log1pt (x : ℝ) (n N : ℕ) (hx : -1 < x)
    (hn : 0 < n) :
    Real.log (((n * N : ℕ) : ℝ) + 1 + x) - Real.log ((N : ℝ) + 1 + x) -
      Real.log (n : ℝ) =
      Real.log (1 + ((1 - (n : ℝ)) * (1 + x)) / ((n : ℝ) * ((N : ℝ) + 1 + x))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hx0_pos := chapter8_x0_pos x N hx
  have hx1_pos := chapter8_x1_pos x n N hx
  have hx0_ne : ((N : ℝ) + 1 + x) ≠ 0 := ne_of_gt hx0_pos
  have hx1_ne : (((n * N : ℕ) : ℝ) + 1 + x) ≠ 0 := ne_of_gt hx1_pos
  have hcast : ((n * N : ℕ) : ℝ) = (n : ℝ) * (N : ℝ) := Nat.cast_mul n N
  have h1pt_eq : (1 + ((1 - (n : ℝ)) * (1 + x)) /
      ((n : ℝ) * ((N : ℝ) + 1 + x))) =
      (((n * N : ℕ) : ℝ) + 1 + x) / ((n : ℝ) * ((N : ℝ) + 1 + x)) := by
    field_simp
    rw [hcast]
    ring
  have hlog1 : Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      Real.log ((N : ℝ) + 1 + x) =
      Real.log ((((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)) := by
    rw [Real.log_div hx1_ne hx0_ne]
  have hnx0_ne : (n : ℝ) * ((N : ℝ) + 1 + x) ≠ 0 :=
    mul_ne_zero hn_ne hx0_ne
  have hlog2 : Real.log ((((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)) -
      Real.log (n : ℝ) =
      Real.log ((((n * N : ℕ) : ℝ) + 1 + x) / ((n : ℝ) * ((N : ℝ) + 1 + x))) := by
    have hdiv_ne : ((((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)) ≠ 0 :=
      div_ne_zero hx1_ne hx0_ne
    rw [← Real.log_div hdiv_ne hn_ne]
    congr 1
    field_simp
  rw [h1pt_eq]
  linear_combination hlog1 + hlog2

/-- `delta_N * L1 → 0`. -/
private theorem chapter8_delta_mul_L1_tendsto (x : ℝ) (n : ℕ) (hx : -1 < x)
    (hn : 0 < n) :
    Tendsto (fun N : ℕ => (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      Real.log ((N : ℝ) + 1 + x) - Real.log (n : ℝ)) *
      Real.log (((n * N : ℕ) : ℝ) + 1 + x)) atTop (𝓝 0) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hL1x0 := chapter8_L1_div_x0_tendsto x n hx hn
  have hK : Tendsto (fun N : ℕ => (2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ)) *
      (Real.log (((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)))
      atTop (𝓝 0) := by
    have hmul := hL1x0.const_mul (2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ))
    simpa using hmul
  have hKneg : Tendsto (fun N : ℕ => -((2 * |(1 - (n : ℝ)) * (1 + x)| /
      (n : ℝ)) * (Real.log (((n * N : ℕ) : ℝ) + 1 + x) /
      ((N : ℝ) + 1 + x)))) atTop (𝓝 0) := by
    simpa using hK.neg
  have hev_x0 : ∀ᶠ N : ℕ in atTop, 3 ≤ (N : ℝ) + 1 + x :=
    (chapter8_A_tendsto_atTop x).eventually (eventually_ge_atTop 3)
  have hev_x1 : ∀ᶠ N : ℕ in atTop, 3 ≤ ((n * N : ℕ) : ℝ) + 1 + x :=
    (chapter8_B_tendsto_atTop x n hn).eventually (eventually_ge_atTop 3)
  have hev_big : ∀ᶠ N : ℕ in atTop,
      2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ) ≤ (N : ℝ) + 1 + x :=
    (chapter8_A_tendsto_atTop x).eventually
      (eventually_ge_atTop (2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ)))
  have hev_le : ∀ᶠ N : ℕ in atTop,
      -((2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ)) *
        (Real.log (((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x))) ≤
      (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
        Real.log ((N : ℝ) + 1 + x) - Real.log (n : ℝ)) *
        Real.log (((n * N : ℕ) : ℝ) + 1 + x) ∧
      (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
        Real.log ((N : ℝ) + 1 + x) - Real.log (n : ℝ)) *
        Real.log (((n * N : ℕ) : ℝ) + 1 + x) ≤
      (2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ)) *
        (Real.log (((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)) := by
    filter_upwards [hev_x0, hev_x1, hev_big] with N hx0_3 hx1_3 hbig
    have hx0_pos := chapter8_x0_pos x N hx
    have hx1_pos := chapter8_x1_pos x n N hx
    have hx0_ne : ((N : ℝ) + 1 + x) ≠ 0 := ne_of_gt hx0_pos
    have hx1_ne : (((n * N : ℕ) : ℝ) + 1 + x) ≠ 0 := ne_of_gt hx1_pos
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hcast : ((n * N : ℕ) : ℝ) = (n : ℝ) * (N : ℝ) := Nat.cast_mul n N
    have hnx0_pos : (0 : ℝ) < (n : ℝ) * ((N : ℝ) + 1 + x) :=
      mul_pos hnR hx0_pos
    have hL1_nonneg : 0 ≤ Real.log (((n * N : ℕ) : ℝ) + 1 + x) := by
      apply Real.log_nonneg
      linarith
    have h1pt_eq : (1 + ((1 - (n : ℝ)) * (1 + x)) /
        ((n : ℝ) * ((N : ℝ) + 1 + x))) =
        (((n * N : ℕ) : ℝ) + 1 + x) / ((n : ℝ) * ((N : ℝ) + 1 + x)) := by
      field_simp
      rw [hcast]
      ring
    have h1pt_pos : (0 : ℝ) < 1 + ((1 - (n : ℝ)) * (1 + x)) /
        ((n : ℝ) * ((N : ℝ) + 1 + x)) := by
      rw [h1pt_eq]
      exact div_pos hx1_pos hnx0_pos
    have ht_abs : |((1 - (n : ℝ)) * (1 + x)) /
        ((n : ℝ) * ((N : ℝ) + 1 + x))| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hnx0_pos]
      rw [div_le_iff₀ hnx0_pos]
      have h2C : (2 : ℝ) * |(1 - (n : ℝ)) * (1 + x)| ≤
          (n : ℝ) * ((N : ℝ) + 1 + x) := by
        have hdiv := hbig
        rw [div_le_iff₀ hnR] at hdiv
        linarith [hdiv]
      linarith [h2C]
    have hdelta_eq := chapter8_delta_eq_log1pt x n N hx hn
    have hlog_bound : |Real.log (1 + ((1 - (n : ℝ)) * (1 + x)) /
        ((n : ℝ) * ((N : ℝ) + 1 + x)))| ≤
        2 * |((1 - (n : ℝ)) * (1 + x)) /
          ((n : ℝ) * ((N : ℝ) + 1 + x))| :=
      chapter8_log_one_add_bound ht_abs h1pt_pos
    have ht_eq : |((1 - (n : ℝ)) * (1 + x)) /
        ((n : ℝ) * ((N : ℝ) + 1 + x))| =
        |(1 - (n : ℝ)) * (1 + x)| / ((n : ℝ) * ((N : ℝ) + 1 + x)) := by
      rw [abs_div, abs_of_pos hnx0_pos]
    have habs_L1 : |Real.log (((n * N : ℕ) : ℝ) + 1 + x)| =
        Real.log (((n * N : ℕ) : ℝ) + 1 + x) :=
      abs_of_nonneg hL1_nonneg
    have h_abs_le : |(Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
        Real.log ((N : ℝ) + 1 + x) - Real.log (n : ℝ)) *
        Real.log (((n * N : ℕ) : ℝ) + 1 + x)| ≤
        (2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ)) *
        (Real.log (((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)) := by
      rw [hdelta_eq, abs_mul, habs_L1]
      have hle1 : |Real.log (1 + ((1 - (n : ℝ)) * (1 + x)) /
          ((n : ℝ) * ((N : ℝ) + 1 + x)))| *
          Real.log (((n * N : ℕ) : ℝ) + 1 + x) ≤
          (2 * (|(1 - (n : ℝ)) * (1 + x)| /
            ((n : ℝ) * ((N : ℝ) + 1 + x)))) *
          Real.log (((n * N : ℕ) : ℝ) + 1 + x) := by
        apply mul_le_mul_of_nonneg_right _ hL1_nonneg
        linarith [hlog_bound, ht_eq]
      have heq2 : (2 * (|(1 - (n : ℝ)) * (1 + x)| /
          ((n : ℝ) * ((N : ℝ) + 1 + x)))) *
          Real.log (((n * N : ℕ) : ℝ) + 1 + x) =
          (2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ)) *
          (Real.log (((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)) := by
        field_simp
      linarith [hle1, heq2]
    exact abs_le.mp h_abs_le
  have hev_lo : ∀ᶠ N : ℕ in atTop,
      -((2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ)) *
        (Real.log (((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x))) ≤
      (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
        Real.log ((N : ℝ) + 1 + x) - Real.log (n : ℝ)) *
        Real.log (((n * N : ℕ) : ℝ) + 1 + x) :=
    hev_le.mono (fun N h => h.1)
  have hev_hi : ∀ᶠ N : ℕ in atTop,
      (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
        Real.log ((N : ℝ) + 1 + x) - Real.log (n : ℝ)) *
        Real.log (((n * N : ℕ) : ℝ) + 1 + x) ≤
      (2 * |(1 - (n : ℝ)) * (1 + x)| / (n : ℝ)) *
        (Real.log (((n * N : ℕ) : ℝ) + 1 + x) / ((N : ℝ) + 1 + x)) :=
    hev_le.mono (fun N h => h.2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hKneg hK hev_lo hev_hi

/-- Integral formula `I_N = (L1^2 - L2^2)/2`. -/
private theorem chapter8_I_eq (x : ℝ) (n N : ℕ) (hx : -1 < x) (hn : 0 < n) :
    (∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x), Real.log t / t) =
      (Real.log (((n * N : ℕ) : ℝ) + 1 + x)) ^ 2 / 2 -
        (Real.log ((N : ℝ) + 1 + x)) ^ 2 / 2 := by
  have hx0_pos := chapter8_x0_pos x N hx
  have hle := chapter8_N_le_nN n N hn
  have hleR : (N : ℝ) ≤ ((n * N : ℕ) : ℝ) := Nat.cast_le.mpr hle
  have hab : (N : ℝ) + 1 + x ≤ ((n * N : ℕ) : ℝ) + 1 + x := by linarith
  exact chapter8_log_div_integral hx0_pos hab

/-- Middle term `I_N - log n * L1 → -(log n)^2 / 2`. -/
private theorem chapter8_middle_tendsto (x : ℝ) (n : ℕ) (hx : -1 < x)
    (hn : 0 < n) :
    Tendsto (fun N : ℕ => (∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) +
      1 + x), Real.log t / t) -
      Real.log (n : ℝ) * Real.log (((n * N : ℕ) : ℝ) + 1 + x))
      atTop (𝓝 (-((Real.log (n : ℝ)) ^ 2 / 2))) := by
  have hD := chapter8_D_tendsto x n hx hn
  have hD2 : Tendsto (fun N : ℕ => (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      Real.log ((N : ℝ) + 1 + x)) ^ 2) atTop (𝓝 ((Real.log (n : ℝ)) ^ 2)) :=
    hD.pow 2
  have hD2d : Tendsto (fun N : ℕ => (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      Real.log ((N : ℝ) + 1 + x)) ^ 2 / 2)
      atTop (𝓝 ((Real.log (n : ℝ)) ^ 2 / 2)) :=
    hD2.div_const 2
  have hdel := chapter8_delta_mul_L1_tendsto x n hx hn
  have hsub : Tendsto (fun N : ℕ => (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      Real.log ((N : ℝ) + 1 + x) - Real.log (n : ℝ)) *
      Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
        Real.log ((N : ℝ) + 1 + x)) ^ 2 / 2)
      atTop (𝓝 (0 - (Real.log (n : ℝ)) ^ 2 / 2)) :=
    hdel.sub hD2d
  have hsub0 : Tendsto (fun N : ℕ => (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      Real.log ((N : ℝ) + 1 + x) - Real.log (n : ℝ)) *
      Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      (Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
        Real.log ((N : ℝ) + 1 + x)) ^ 2 / 2)
      atTop (𝓝 (-((Real.log (n : ℝ)) ^ 2 / 2))) := by
    simpa using hsub
  refine Tendsto.congr' ?_ hsub0
  filter_upwards with N
  rw [chapter8_I_eq x n N hx hn]
  ring

/-- `n * N → ∞` as `N → ∞` for `0 < n`. -/
private theorem chapter8_n_mul_tendsto (n : ℕ) (hn : 0 < n) :
    Tendsto (fun N : ℕ => n * N) atTop atTop :=
  tendsto_atTop_mono (fun N => chapter8_N_le_nN n N hn) tendsto_id

/-- `(n*N : ℝ) + x → ∞`. -/
private theorem chapter8_Y_tendsto_atTop (x : ℝ) (n : ℕ) (hn : 0 < n) :
    Tendsto (fun N : ℕ => ((n * N : ℕ) : ℝ) + x) atTop atTop := by
  have hB := chapter8_B_tendsto_atTop x n hn
  have hY : Tendsto (fun N : ℕ => (((n * N : ℕ) : ℝ) + 1 + x) + (-1))
      atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1) hB
  refine Tendsto.congr' ?_ hY
  filter_upwards with N
  ring

/-- `log (nN+x) - L1 → 0`. -/
private theorem chapter8_logdiff_tendsto (x : ℝ) (n : ℕ) (hn : 0 < n) :
    Tendsto (fun N : ℕ => Real.log (((n * N : ℕ) : ℝ) + x) -
      Real.log (((n * N : ℕ) : ℝ) + 1 + x)) atTop (𝓝 0) := by
  have hY := chapter8_Y_tendsto_atTop x n hn
  have hlog : Tendsto (fun N : ℕ => Real.log ((((n * N : ℕ) : ℝ) + x) + 1) -
      Real.log (((n * N : ℕ) : ℝ) + x)) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log 1).comp hY
  have hlog' : Tendsto (fun N : ℕ => Real.log (((n * N : ℕ) : ℝ) + 1 + x) -
      Real.log (((n * N : ℕ) : ℝ) + x)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hlog
    filter_upwards with N
    have heq : ((((n * N : ℕ) : ℝ) + x) + 1) =
        (((n * N : ℕ) : ℝ) + 1 + x) := by ring
    rw [heq]
  simpa using hlog'.neg

/-- `H_{nN} - L1 → -psi (x+1)`. -/
private theorem chapter8_H_sub_L1_tendsto (x : ℝ) (hx : -1 < x) (n : ℕ)
    (hn : 0 < n) :
    Tendsto (fun N : ℕ => (∑ i ∈ Finset.range (n * N),
      1 / (((i : ℝ) + 1) + x)) -
      Real.log (((n * N : ℕ) : ℝ) + 1 + x))
      atTop (𝓝 (-chapter8RealDigamma (x + 1))) := by
  have hH : Tendsto (fun N : ℕ => (∑ i ∈ Finset.range (n * N),
      1 / (((i : ℝ) + 1) + x)) -
      Real.log (((n * N : ℕ) : ℝ) + x))
      atTop (𝓝 (-chapter8RealDigamma (x + 1))) :=
    (chapter8_harmonic_limit x hx).comp (chapter8_n_mul_tendsto n hn)
  have hdiff := chapter8_logdiff_tendsto x n hn
  have hadd : Tendsto (fun N : ℕ => ((∑ i ∈ Finset.range (n * N),
      1 / (((i : ℝ) + 1) + x)) -
      Real.log (((n * N : ℕ) : ℝ) + x)) +
      (Real.log (((n * N : ℕ) : ℝ) + x) -
        Real.log (((n * N : ℕ) : ℝ) + 1 + x)))
      atTop (𝓝 ((-chapter8RealDigamma (x + 1)) + 0)) :=
    hH.add hdiff
  have hadd0 : Tendsto (fun N : ℕ => ((∑ i ∈ Finset.range (n * N),
      1 / (((i : ℝ) + 1) + x)) -
      Real.log (((n * N : ℕ) : ℝ) + x)) +
      (Real.log (((n * N : ℕ) : ℝ) + x) -
        Real.log (((n * N : ℕ) : ℝ) + 1 + x)))
      atTop (𝓝 (-chapter8RealDigamma (x + 1))) := by
    simpa using hadd
  refine Tendsto.congr' ?_ hadd0
  filter_upwards with N
  ring

/-- Right side converges to the goal right side. -/
private theorem chapter8_RHS_tendsto (x : ℝ) (n : ℕ) (hx : -1 < x) (hn : 0 < n) :
    Tendsto (fun N : ℕ => (n : ℝ) *
        ((∑ i ∈ Finset.range (n * N),
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
        (∑ i ∈ Finset.range N,
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
        (n : ℝ) * Real.log n *
        (∑ i ∈ Finset.range (n * N), 1 / (((i : ℝ) + 1) + x)))
      atTop (𝓝 ((n : ℝ) * Real.log n * chapter8RealDigamma (x + 1) -
        (n : ℝ) * Real.log n ^ 2 / 2)) := by
  have hA0 := chapter8_S_sub_I_tendsto x n hn
  have hA : Tendsto (fun N : ℕ => (n : ℝ) *
      (((∑ i ∈ Finset.range (n * N),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
      (∑ i ∈ Finset.range N,
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
      (∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
        Real.log t / t))) atTop (𝓝 0) := by
    have hmul := hA0.const_mul (n : ℝ)
    simpa using hmul
  have hB0 := chapter8_middle_tendsto x n hx hn
  have hB : Tendsto (fun N : ℕ => (n : ℝ) *
      ((∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
        Real.log t / t) -
      Real.log (n : ℝ) * Real.log (((n * N : ℕ) : ℝ) + 1 + x)))
      atTop (𝓝 ((n : ℝ) * (-((Real.log (n : ℝ)) ^ 2 / 2)))) :=
    hB0.const_mul (n : ℝ)
  have hC0 := chapter8_H_sub_L1_tendsto x hx n hn
  have hC : Tendsto (fun N : ℕ => (-((n : ℝ) * Real.log n)) *
      ((∑ i ∈ Finset.range (n * N), 1 / (((i : ℝ) + 1) + x)) -
      Real.log (((n * N : ℕ) : ℝ) + 1 + x)))
      atTop (𝓝 ((-((n : ℝ) * Real.log n)) * (-chapter8RealDigamma (x + 1)))) :=
    hC0.const_mul (-((n : ℝ) * Real.log n))
  have hAB : Tendsto (fun N : ℕ => (n : ℝ) *
      (((∑ i ∈ Finset.range (n * N),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
      (∑ i ∈ Finset.range N,
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
      (∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
        Real.log t / t)) +
      (n : ℝ) * ((∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
        Real.log t / t) -
      Real.log (n : ℝ) * Real.log (((n * N : ℕ) : ℝ) + 1 + x)))
      atTop (𝓝 (0 + (n : ℝ) * (-((Real.log (n : ℝ)) ^ 2 / 2)))) :=
    hA.add hB
  have hABC : Tendsto (fun N : ℕ => ((n : ℝ) *
      (((∑ i ∈ Finset.range (n * N),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
      (∑ i ∈ Finset.range N,
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
      (∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
        Real.log t / t)) +
      (n : ℝ) * ((∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
        Real.log t / t) -
      Real.log (n : ℝ) * Real.log (((n * N : ℕ) : ℝ) + 1 + x))) +
      (-((n : ℝ) * Real.log n)) *
      ((∑ i ∈ Finset.range (n * N), 1 / (((i : ℝ) + 1) + x)) -
      Real.log (((n * N : ℕ) : ℝ) + 1 + x)))
      atTop (𝓝 ((0 + (n : ℝ) * (-((Real.log (n : ℝ)) ^ 2 / 2))) +
        ((-((n : ℝ) * Real.log n)) * (-chapter8RealDigamma (x + 1))))) :=
    hAB.add hC
  have hABC' : Tendsto (fun N : ℕ => ((n : ℝ) *
      (((∑ i ∈ Finset.range (n * N),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
      (∑ i ∈ Finset.range N,
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
      (∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
        Real.log t / t)) +
      (n : ℝ) * ((∫ t in ((N : ℝ) + 1 + x)..(((n * N : ℕ) : ℝ) + 1 + x),
        Real.log t / t) -
      Real.log (n : ℝ) * Real.log (((n * N : ℕ) : ℝ) + 1 + x))) +
      (-((n : ℝ) * Real.log n)) *
      ((∑ i ∈ Finset.range (n * N), 1 / (((i : ℝ) + 1) + x)) -
      Real.log (((n * N : ℕ) : ℝ) + 1 + x)))
      atTop (𝓝 ((n : ℝ) * Real.log n * chapter8RealDigamma (x + 1) -
        (n : ℝ) * Real.log n ^ 2 / 2)) := by
    convert hABC using 2
    ring
  refine Tendsto.congr' ?_ hABC'
  filter_upwards with N
  ring

/-- **Ramanujan's multiplication formula for the series $\sum_k (\log k/k - \log(k+x)/(k+x))$.**
For real $x$ let
$$\varphi(x) = \sum_{k=1}^{\infty} \left(\frac{\log k}{k} - \frac{\log(k+x)}{k+x}\right),$$
and let $\psi(x) = \Gamma'(x)/\Gamma(x)$. Let $x > -1$ be real and let $n \ge 1$ be an integer.
Then $k + x > 0$ and $k + (x - j)/n > 0$ for all integers $k \ge 1$ and $0 \le j < n$; the series
defining $\varphi(x)$ and $\varphi((x - j)/n)$ for $0 \le j < n$ converge absolutely;
$\Gamma(x + 1) > 0$; and
$$n \varphi(x) - \sum_{j=0}^{n-1} \varphi\left(\frac{x - j}{n}\right) =
n \log n \, \psi(x + 1) - \frac{n (\log n)^2}{2}.$$

Proves `Wanted` entry `ramanujan_part1_ch8_entry17_loggammaintegral`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.
-/
theorem ramanujan_part1_ch8_entry17_loggammaintegral (x : ℝ) (n : ℕ)
    (hx : -1 < x) (hn : 0 < n) :
    (∀ j : ℕ, 0 < (j + 1 : ℝ) + x) ∧
      (∀ k ∈ range n, ∀ j : ℕ,
        0 < (j + 1 : ℝ) + (x - k) / n) ∧
      Summable (chapter8Entry17Term x) ∧
      (∀ k ∈ range n,
        Summable (chapter8Entry17Term ((x - k) / n))) ∧
      0 < Real.Gamma (x + 1) ∧
      (n : ℝ) * chapter8Entry17Phi x -
          ∑ k ∈ range n, chapter8Entry17Phi ((x - k) / n) =
        (n : ℝ) * Real.log n * chapter8RealDigamma (x + 1) -
          (n : ℝ) * Real.log n ^ 2 / 2 := by
  have h1 : ∀ j : ℕ, 0 < (j + 1 : ℝ) + x := chapter8_aux_pos1 x hx
  have h2 : ∀ k ∈ range n, ∀ j : ℕ, 0 < (j + 1 : ℝ) + (x - k) / n :=
    chapter8_aux_pos2 x n hx hn
  have h3 : Summable (chapter8Entry17Term x) := chapter8_aux_summable x hx
  have h4 : ∀ k ∈ range n, Summable (chapter8Entry17Term ((x - k) / n)) := by
    intro k hk
    apply chapter8_aux_summable
    rw [Finset.mem_range] at hk
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hkn : (k : ℝ) ≤ (n : ℝ) - 1 := by
      have h1 : k + 1 ≤ n := hk
      have h2 : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    rw [lt_div_iff₀ hnR]
    nlinarith
  have h5 : 0 < Real.Gamma (x + 1) := chapter8_aux_gamma x hx
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  have hL := chapter8_LHS_tendsto x n h3 h4
  have hR := chapter8_RHS_tendsto x n hx hn
  have hEq : ∀ N : ℕ, ((n : ℝ) *
      (∑ j ∈ Finset.range N, chapter8Entry17Term x j) -
      ∑ k ∈ Finset.range n,
        (∑ j ∈ Finset.range N, chapter8Entry17Term ((x - k) / n) j)) =
      ((n : ℝ) *
        ((∑ i ∈ Finset.range (n * N),
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
        (∑ i ∈ Finset.range N,
          Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
        (n : ℝ) * Real.log n *
        (∑ i ∈ Finset.range (n * N), 1 / (((i : ℝ) + 1) + x))) :=
    fun N => chapter8_truncated_identity x n N hx hn
  have hEq' : (fun N : ℕ => (n : ℝ) *
      ((∑ i ∈ Finset.range (n * N),
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x)) -
      (∑ i ∈ Finset.range N,
        Real.log (((i : ℝ) + 1) + x) / (((i : ℝ) + 1) + x))) -
      (n : ℝ) * Real.log n *
      (∑ i ∈ Finset.range (n * N), 1 / (((i : ℝ) + 1) + x))) =ᶠ[atTop]
      (fun N : ℕ => (n : ℝ) *
        (∑ j ∈ Finset.range N, chapter8Entry17Term x j) -
        ∑ k ∈ Finset.range n,
          (∑ j ∈ Finset.range N, chapter8Entry17Term ((x - k) / n) j)) :=
    Eventually.of_forall (fun N => (hEq N).symm)
  have hR' : Tendsto (fun N : ℕ => (n : ℝ) *
      (∑ j ∈ Finset.range N, chapter8Entry17Term x j) -
      ∑ k ∈ Finset.range n,
        (∑ j ∈ Finset.range N, chapter8Entry17Term ((x - k) / n) j))
      atTop (𝓝 ((n : ℝ) * Real.log n * chapter8RealDigamma (x + 1) -
        (n : ℝ) * Real.log n ^ 2 / 2)) :=
    Tendsto.congr' hEq' hR
  exact tendsto_nhds_unique hL hR'

end
end Entry17Loggammaintegral
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end

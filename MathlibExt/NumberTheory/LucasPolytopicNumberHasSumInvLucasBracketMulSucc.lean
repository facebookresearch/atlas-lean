/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.LucasnomialSum
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sum of reciprocals of consecutive Lucas brackets

The reciprocal-product series has a sum expressed through the Lucas logarithm series.
A geometric bound proves summability of the logarithm series used in the formula.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 13 (arXiv `2501.11490`).
-/

namespace MetaMathlibExt

private theorem bracket_succ (P : LucasParameters) (x y : ℝ)
    (hsum : x + y = P.s) (hprod : x * y = -P.t) (n : ℕ) :
    lucasBracket P (n + 1) = x * lucasBracket P n + y ^ n := by
  induction n with
  | zero => simp [lucasBracket, lucasBracketAux]
  | succ n ih =>
    change P.s * lucasBracket P (n + 1) + P.t * lucasBracket P n = _
    rw [← hsum, (by linarith : P.t = -(x * y)), pow_succ]
    linear_combination y * ih

private theorem bracket_closed (P : LucasParameters) (x y : ℝ)
    (hsum : x + y = P.s) (hprod : x * y = -P.t) (n : ℕ) :
    (x - y) * lucasBracket P n = x ^ n - y ^ n := by
  induction n with
  | zero => simp [lucasBracket, lucasBracketAux]
  | succ n ih =>
    rw [bracket_succ P x y hsum hprod, pow_succ, pow_succ]
    linear_combination x * ih

private theorem log_term_eq (P : LucasParameters) (x y : ℝ)
    (hsum : x + y = P.s) (hprod : x * y = -P.t) (hx : x ≠ 0)
    (hxy : x - y ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    (-x / P.t) ^ n / lucasBracket P n =
      (x - y) * (-1 / P.t) ^ n / (1 - (y / x) ^ n) := by
  have ha := lucasBracket_ne_zero P hn
  have hclosed := bracket_closed P x y hsum hprod n
  have hden : x ^ n * (1 - (y / x) ^ n) = (x - y) * lucasBracket P n := by
    rw [hclosed, div_pow]
    field_simp
  have hd : 1 - (y / x) ^ n ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hden
    exact mul_ne_zero hxy ha hden.symm
  have hpow : (-x / P.t) ^ n = x ^ n * (-1 / P.t) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hpow]
  apply (div_eq_div_iff ha hd).2
  linear_combination (-1 / P.t) ^ n * hden

private theorem summable_log_terms (P : LucasParameters) (x y : ℝ)
    (hsum : x + y = P.s) (hprod : x * y = -P.t) (hx : x ≠ 0)
    (hxy : x - y ≠ 0) (hq : |y / x| < 1) (ht : 1 < |P.t|) :
    Summable (fun n : ℕ => (-x / P.t) ^ (n + 1) / lucasBracket P (n + 1)) := by
  have hrat : |(-1 / P.t : ℝ)| < 1 := by
    rw [abs_div, abs_neg, abs_one]
    exact (div_lt_one (by linarith : 0 < |P.t|)).2 ht
  have hgeom : Summable (fun n : ℕ => |(-1 / P.t : ℝ)| ^ n) :=
    summable_geometric_of_abs_lt_one (by simpa only [abs_abs] using hrat)
  have hmajor : Summable (fun n : ℕ =>
      (|x - y| / (1 - |y / x|)) * |(-1 / P.t : ℝ)| ^ (n + 1)) :=
    ((summable_nat_add_iff 1).2 hgeom).mul_left _
  apply hmajor.of_norm_bounded
  intro n
  have hpow : |(y / x) ^ (n + 1)| ≤ |y / x| := by
    rw [abs_pow, pow_succ]
    simpa using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (n := n) (abs_nonneg (y / x)) hq.le) (abs_nonneg (y / x))
  have hden : 1 - |y / x| ≤ 1 - (y / x) ^ (n + 1) := by
    exact sub_le_sub_left ((le_abs_self _).trans hpow) 1
  have hdenpos : 0 < 1 - (y / x) ^ (n + 1) := lt_of_lt_of_le (sub_pos.mpr hq) hden
  rw [Real.norm_eq_abs, log_term_eq P x y hsum hprod hx hxy _ (Nat.succ_ne_zero n),
    abs_div, abs_mul, abs_pow, abs_of_pos hdenpos]
  calc
    |x - y| * |(-1 / P.t : ℝ)| ^ (n + 1) / (1 - (y / x) ^ (n + 1)) ≤
        |x - y| * |(-1 / P.t : ℝ)| ^ (n + 1) / (1 - |y / x|) :=
      div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
        (sub_pos.mpr hq) hden
    _ = _ := by ring

private theorem reciprocal_product_eq (P : LucasParameters) (x y : ℝ)
    (hsum : x + y = P.s) (hprod : x * y = -P.t) (n : ℕ) :
    1 / (lucasBracket P (n + 1) * lucasBracket P (n + 2)) =
      (-x / P.t) ^ (n + 1) / lucasBracket P (n + 1) +
        P.t * ((-x / P.t) ^ (n + 2) / lucasBracket P (n + 2)) := by
  have ha := lucasBracket_ne_zero P (Nat.succ_ne_zero n)
  have hb := lucasBracket_ne_zero P (Nat.succ_ne_zero (n + 1))
  have hcy : (-x / P.t) * y = 1 := by
    field_simp [P.t_ne_zero]
    linarith
  have hp : (-x / P.t) ^ (n + 1) * y ^ (n + 1) = 1 := by
    rw [← mul_pow, hcy, one_pow]
  have hr := bracket_succ P x y hsum hprod (n + 1)
  rw [pow_succ (-x / P.t) (n + 1)]
  field_simp [ha, hb, P.t_ne_zero]
  linear_combination (-((-x / P.t) ^ (n + 1))) * hr - hp

private theorem hasSum_with_roots (P : LucasParameters) (x y : ℝ)
    (hsum : x + y = P.s) (hprod : x * y = -P.t) (hx : x ≠ 0)
    (hxy : x - y ≠ 0) (hq : |y / x| < 1) (ht : 1 < |P.t|) :
    HasSum (fun n : ℕ => 1 / (lucasBracket P (n + 1) * lucasBracket P (n + 2)))
      (x - (1 + P.t) * -∑' n : ℕ, (-x / P.t) ^ (n + 1) / lucasBracket P (n + 1)) := by
  let f : ℕ → ℝ := fun n => (-x / P.t) ^ (n + 1) / lucasBracket P (n + 1)
  have hf : Summable f := summable_log_terms P x y hsum hprod hx hxy hq ht
  have hshift : HasSum (fun n => f (n + 1)) ((∑' n, f n) - f 0) := by
    simpa only [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).2 hf.hasSum
  have hsum' := hf.hasSum.add (hshift.mul_left P.t)
  have hzero : f 0 = -x / P.t := by simp [f, lucasBracket, lucasBracketAux]
  have hvalue : (∑' n, f n) + P.t * ((∑' n, f n) - f 0) =
      x - (1 + P.t) * -(∑' n, f n) := by
    rw [hzero]
    field_simp [P.t_ne_zero]
    ring
  rw [hvalue] at hsum'
  exact hsum'.congr_fun (fun n => reciprocal_product_eq P x y hsum hprod n)

/-- **Sum of reciprocals of products of consecutive Lucas brackets.** Let $(s, t)$ be
nondegenerate Lucas parameters with $s > 0$, $s^2 + 4t > 0$ and $|t| > 1$, write $\{n\}_{s,t}$
for the Lucas brackets and let $\varphi = (s + \sqrt{s^2 + 4t})/2$. Then the series
$\sum_{n \ge 1} 1/(\{n\}_{s,t}\{n+1\}_{s,t})$ converges absolutely, and its sum is
$\varphi - (1 + t)\ln_{s,t}(1 + \varphi/t)$, where
$\ln_{s,t}(1 + \varphi/t) = -\sum_{n \ge 1} (-\varphi/t)^n/\{n\}_{s,t}$ is the Lucas logarithm.

The hypotheses $s > 0$ and $s^2 + 4t > 0$ make $\varphi$ real with $0 < |q| < 1$, where
$q = \varphi'/\varphi$ and $\varphi' = (s - \sqrt{s^2 + 4t})/2$; and $|t| > 1$ puts $-\varphi/t$ in
the paper's convergence range $(-|\varphi|, |\varphi|)$ of the Lucas logarithm. Without
$|t| > 1$ the logarithm series diverges: for $s = t = 1$ its terms $(-\varphi)^n/F_n$, with $F_n$
the Fibonacci numbers, do not tend to $0$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 13
(`jis-2025-25.5.6-thm-13`). -/
public theorem hasSum_inv_lucasBracket_mul_succ (P : LucasParameters) (hs : 0 < P.s)
    (hdisc : 0 < P.s ^ 2 + 4 * P.t) (ht : 1 < |P.t|) :
    HasSum (fun n : ℕ => 1 / (lucasBracket P (n + 1) * lucasBracket P (n + 2)))
      ((P.s + Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2 -
        (1 + P.t) * -∑' n : ℕ, (-((P.s + Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) / P.t) ^ (n + 1) /
          lucasBracket P (n + 1))
    := by
  let x := (P.s + Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2
  let y := (P.s - Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2
  have hdpos := Real.sqrt_pos.2 hdisc
  have hdsq := Real.sq_sqrt hdisc.le
  have hsum : x + y = P.s := by dsimp [x, y]; ring
  have hprod : x * y = -P.t := by dsimp [x, y]; nlinarith
  have hx : 0 < x := by dsimp [x]; linarith
  have hxy : 0 < x - y := by dsimp [x, y]; linarith
  have hq : |y / x| < 1 := by
    rw [abs_div, abs_of_pos hx, div_lt_one hx]
    apply abs_lt.2
    dsimp [x, y]
    constructor <;> linarith
  exact hasSum_with_roots P x y hsum hprod hx.ne' hxy.ne' hq ht

end MetaMathlibExt

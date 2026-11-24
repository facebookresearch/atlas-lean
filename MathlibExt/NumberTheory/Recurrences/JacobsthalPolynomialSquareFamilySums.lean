/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Analysis.SpecificLimits.Normed
import MathlibExt.NumberTheory.BinetClosedForm
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Reciprocal sums of shifted Jacobsthal polynomial squares

The generalized Catalan identity turns both Jacobsthal and Jacobsthal–Lucas summands into
differences of shifted ratios. The dominant root of the recurrence gives their common limit.
-/

namespace MetaMathlibExt

open Filter Polynomial
open scoped Topology

local notation "𝔍" => generalizedFibonacciPolynomial 0 1 1 X
local notation "𝔧" => generalizedFibonacciPolynomial 2 1 1 X

namespace tsum_jacobsthalPoly_sq_sub_family

private theorem tendsto_ratio {x : ℝ} (hx : 0 < x) (G : ℕ → ℝ)
    (hrec : ∀ n, G (n + 2) = 1 * G (n + 1) + x * G n)
    (h₀ : 0 ≤ G 0) (h₁ : 0 < G 1) (r : ℕ) :
    Tendsto (fun n => G (n + r) / G n) atTop (𝓝 (((1 + √(4 * x + 1)) / 2) ^ r)) := by
  let w := (1 + √(4 * x + 1)) / 2
  let v := (1 - √(4 * x + 1)) / 2
  have hD : 1 < √(4 * x + 1) := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have hw : 0 < w := by dsimp [w]; linarith
  have hv : v < 0 := by dsimp [v]; linarith
  have hvw := hv.trans hw
  have hq : |v / w| < 1 := by
    rw [abs_div, abs_of_neg hv, abs_of_pos hw, div_lt_one hw]
    dsimp [v, w]
    linarith
  let A := G 1 - v * G 0
  let B := G 1 - w * G 0
  have hA : 0 < A := sub_pos.mpr ((mul_nonpos_of_nonpos_of_nonneg hv.le h₀).trans_lt h₁)
  have hroot := Real.sq_sqrt (show 0 ≤ 4 * x + 1 by positivity)
  have hbin := binet_closed_form_second_order G 1 (-x) w v
    (by dsimp [w]; nlinarith) (by dsimp [v]; nlinarith) hvw.ne.symm
    (fun n => by simpa using hrec n)
  have hnorm (n : ℕ) : G n / w ^ n = (A - B * (v / w) ^ n) / (w - v) := by
    rw [hbin, div_pow v w]
    dsimp only [A, B]
    rw [div_right_comm, sub_div, mul_div_cancel_right₀ _ (pow_ne_zero n hw.ne'), mul_div_assoc]
  have hlim : Tendsto (fun n => G n / w ^ n) atTop (𝓝 (A / (w - v))) := by
    simp_rw [hnorm]
    simpa using (((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).const_mul B).const_sub A
      |>.div_const (w - v))
  have hne := (div_pos hA (sub_pos.mpr hvw)).ne'
  have hlim' := ((hlim.comp (tendsto_add_atTop_nat r)).div hlim hne).mul_const (w ^ r)
  simp only [div_self hne, one_mul] at hlim'
  apply hlim'.congr
  intro n
  change G (n + r) / w ^ (n + r) / (G n / w ^ n) * w ^ r = G (n + r) / G n
  rw [pow_add]
  rw [div_div_div_comm, mul_div_cancel_left₀ _ (pow_ne_zero n hw.ne'), div_mul_cancel₀]
  exact pow_ne_zero r hw.ne'

/-- A common scalar times nonnegative terms has the sum given by its partial sums. -/
private theorem hasSum_of_fixed_sign {a L : ℝ} {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a * f n) atTop (𝓝 L)) :
    HasSum (fun n => a * f n) L := by
  rcases le_total 0 a with ha | ha
  · exact (hasSum_iff_tendsto_nat_of_nonneg (fun n => mul_nonneg ha (hf n)) L).2 h
  · have hn : HasSum (fun n => -(a * f n)) (-L) := by
      apply (hasSum_iff_tendsto_nat_of_nonneg (fun n =>
        neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg ha (hf n))) _).2
      simpa only [Finset.sum_neg_distrib] using h.neg
    simpa using hn.neg

private theorem sum_family {x : ℝ} (hx : 0 < x) (G : ℕ → ℝ) (C : ℝ)
    (hrec : ∀ n, G (n + 2) = 1 * G (n + 1) + x * G n)
    (h₀ : 0 ≤ G 0) (h₁ : 0 < G 1) (hC : G 1 * G 1 - G 0 * G 2 = C)
    {k p r t : ℕ} (hk : 0 < k) (hp : 0 < p) (ht₀ : 0 < t) :
    ∑' n : ℕ, ((-1) ^ (t * k) * C) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 r) *
          aeval x (𝔍 (2 * p * k)) /
        (G ((2 * p * n + p + t) * k) ^ 2 -
          ((-1) ^ (t * k) * C) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 (p * k)) ^ 2) =
      G (t * k + r) / G (t * k) - ((1 + √(4 * x + 1)) / 2) ^ r := by
  let J (n : ℕ) := aeval x (𝔍 n)
  have hJ (n : ℕ) : J (n + 2) = 1 * J (n + 1) + x * J n := by simp [J]
  have catalan := horadam_generalized_catalan_identity 1 x G G J hrec hrec hJ
    (by simp [J]) (by simp [J])
  have det (m i j : ℕ) : G (m + i) * G (m + j) - G m * G (m + i + j) =
      (-x) ^ m * C * J j * J i := by
    have h := catalan 0 j 1
    simp only [Nat.zero_add, pow_zero, one_mul, mul_comm (G j) (G 1), hC] at h
    rw [catalan, h]
    ring
  have hpos' (n : ℕ) : 0 ≤ G n ∧ 0 < G (n + 1) := by
    induction n with
    | zero => exact ⟨h₀, h₁⟩
    | succ n ih =>
      refine ⟨ih.2.le, ?_⟩
      rw [hrec, one_mul]
      exact add_pos_of_pos_of_nonneg ih.2 (mul_nonneg hx.le ih.1)
  let e (n : ℕ) := (2 * p * n + t) * k
  have hpos (n : ℕ) : 0 < G (e n) := by
    have he : 0 < e n := Nat.mul_pos (Nat.add_pos_right _ ht₀) hk
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    rw [hm]
    exact (hpos' m).2
  have hnext (n : ℕ) : e (n + 1) = e n + 2 * p * k := by dsimp [e]; ring
  have hsign (n : ℕ) : (-x) ^ e n = (-1) ^ (t * k) * x ^ e n := by
    rw [← neg_one_mul x, mul_pow]
    congr 1
    simp [e, Nat.add_mul, pow_add, Nat.mul_assoc, pow_mul]
  let c := (-1 : ℝ) ^ (t * k) * C * J r * J (2 * p * k)
  let d (n : ℕ) := G ((2 * p * n + p + t) * k) ^ 2 -
    ((-1 : ℝ) ^ (t * k) * C) * x ^ e n * J (p * k) ^ 2
  let R (n : ℕ) := G (e n + r) / G (e n)
  -- Equal shifts factor the denominator as a product of two positive terms.
  have hden (n : ℕ) : d n = G (e n) * G (e (n + 1)) := by
    have h := det (e n) (p * k) (p * k)
    rw [hsign] at h
    dsimp only [d]
    rw [show (2 * p * n + p + t) * k = e n + p * k by dsimp [e]; ring, hnext,
      show e n + 2 * p * k = e n + p * k + p * k by ring]
    linear_combination h
  -- Unequal shifts give the numerator of the difference of ratios.
  have hdiff (n : ℕ) : c * (x ^ e n / d n) = R n - R (n + 1) := by
    dsimp only [R]
    rw [hden, div_sub_div _ _ (hpos n).ne' (hpos (n + 1)).ne', mul_div_assoc']
    congr 1
    rw [hnext, show e n + 2 * p * k + r = e n + r + 2 * p * k by omega, det, hsign]
    dsimp only [c]
    ring
  have hmono : StrictMono e := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hnext]
    exact Nat.lt_add_of_pos_right (by positivity)
  have hlim := (tendsto_ratio hx G hrec h₀ h₁ r).comp hmono.tendsto_atTop
  have hsum : HasSum (fun n => c * (x ^ e n / d n)) (R 0 - ((1 + √(4 * x + 1)) / 2) ^ r) := by
    apply hasSum_of_fixed_sign (fun n => div_nonneg (pow_nonneg hx.le _) ((hden n) ▸
      (mul_pos (hpos n) (hpos (n + 1))).le))
    simp_rw [hdiff, Finset.sum_range_sub']
    exact tendsto_const_nhds.sub hlim
  convert hsum.tsum_eq using 1
  · apply tsum_congr
    intro n
    dsimp only [c, e, J, d]
    ring
  · simp [R, e]

end tsum_jacobsthalPoly_sq_sub_family

set_option linter.unusedVariables false in
/-- **Reciprocal sums of shifted squares of Jacobsthal and Jacobsthal–Lucas polynomials
(Koshy–Gao, Theorem 3.1).** Let $J_n(x)$ and $j_n(x)$ be the Jacobsthal and Jacobsthal–Lucas
polynomials, given by $z_{n+2} = z_{n+1} + x z_n$ with initial values $J_0 = 0$, $J_1 = 1$ and
$j_0 = 2$, $j_1 = 1$. Let $x > 0$ be real, let $k$, $p$, $r$, $t$ be positive integers with
$t \le 2p$, let $w = (1 + \sqrt{4x + 1})/2$, and write $e_n = (2pn + t)k$. Then
$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk} x^{e_n} J_r(x) J_{2pk}(x)}
{J_{(2pn+p+t)k}(x)^2 - (-1)^{tk} x^{e_n} J_{pk}(x)^2} =
\frac{J_{tk+r}(x)}{J_{tk}(x)} - w^r
$$
and
$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk+1} (4x + 1) x^{e_n} J_r(x) J_{2pk}(x)}
{j_{(2pn+p+t)k}(x)^2 + (-1)^{tk} (4x + 1) x^{e_n} J_{pk}(x)^2} =
\frac{j_{tk+r}(x)}{j_{tk}(x)} - w^r.
$$

In the source the sums run over $n \ge 1$, with $(2pn + t - p)k$ in place of $(2pn + p + t)k$
and exponent $(2pn + t - 2p)k$ in place of $e_n$; here the summation index is shifted to start
at $n = 0$.

Source: Thomas Koshy and Zhenguang Gao, *Sums Involving a Family of Jacobsthal Polynomial
Squares*, The Fibonacci Quarterly 62 (2024), Article koshy12202023,
Theorem 3.1 (`fq-2024-koshy12202023-thm-3.1`). -/
public theorem tsum_jacobsthalPoly_sq_sub_family {x : ℝ} (hx : 0 < x) {k p r t : ℕ}
    (hk : 0 < k) (hp : 0 < p) (hr : 0 < r) (ht₀ : 0 < t) (ht : t ≤ 2 * p) :
    ∑' n : ℕ, (-1) ^ (t * k) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 r) *
          aeval x (𝔍 (2 * p * k)) /
        (aeval x (𝔍 ((2 * p * n + p + t) * k)) ^ 2 -
          (-1) ^ (t * k) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 (p * k)) ^ 2) =
      aeval x (𝔍 (t * k + r)) / aeval x (𝔍 (t * k)) - ((1 + √(4 * x + 1)) / 2) ^ r ∧
    ∑' n : ℕ, (-1) ^ (t * k + 1) * (4 * x + 1) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 r) *
          aeval x (𝔍 (2 * p * k)) /
        (aeval x (𝔧 ((2 * p * n + p + t) * k)) ^ 2 +
          (-1) ^ (t * k) * (4 * x + 1) * x ^ ((2 * p * n + t) * k) * aeval x (𝔍 (p * k)) ^ 2) =
      aeval x (𝔧 (t * k + r)) / aeval x (𝔧 (t * k)) - ((1 + √(4 * x + 1)) / 2) ^ r := by
  constructor
  · simpa only [mul_one] using
      tsum_jacobsthalPoly_sq_sub_family.sum_family hx (fun n => aeval x (𝔍 n)) 1
        (fun n => by simp) (by simp) (by simp) (by simp) (r := r) hk hp ht₀
  · simpa only [pow_succ (-1 : ℝ), mul_neg, mul_neg_one, neg_mul, sub_neg_eq_add,
      mul_assoc, one_mul] using
      tsum_jacobsthalPoly_sq_sub_family.sum_family hx (fun n => aeval x (𝔧 n)) (-(4 * x + 1))
        (fun n => by simp) (by norm_num [map_ofNat]) (by simp)
        (by norm_num [generalizedFibonacciPolynomial, map_ofNat]; ring) (r := r) hk hp ht₀

end MetaMathlibExt

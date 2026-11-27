/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Topology.Algebra.Polynomial
import MathlibExt.Analysis.SpecialFunctions.ExpOfContinuousAddMul
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry13CorollarySchroder

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 14

This file proves Ramanujan's Lagrange series, including convergence on the boundary circle.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry14LagrangeSeries

open scoped Interval Topology

/-- **Lagrange series coefficients.** For real numbers $p$, $q$, $n$ and a natural number $k$,
the Lagrange series coefficient $C_{p,q}(n, k)$ is $1$ if $k = 0$, and for $k \ge 1$ it is
$$C_{p,q}(n, k) = n \prod_{j=1}^{k-1} (n + k p - j q)$$
(an empty product when $k = 1$).
-/
def lagrangeSeriesCoefficient (p q n : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else
    n * ∏ j ∈ Finset.range (k - 1), (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)

/-- **Lagrange series coefficient of degree zero.** For all real numbers $p$, $q$, $n$, the
Lagrange series coefficient $C_{p,q}(n, 0)$ of degree $0$ equals $1$. -/
@[simp]
theorem lagrangeSeriesCoefficient_zero (p q n : ℝ) :
    lagrangeSeriesCoefficient p q n 0 = 1 := by
  simp [lagrangeSeriesCoefficient]

/-- **Lagrange series coefficients of positive degree.** For all real numbers $p$, $q$, $n$ and
every natural number $k \ne 0$, the Lagrange series coefficient of degree $k$ is
$$C_{p,q}(n, k) = n \prod_{j=1}^{k-1} (n + k p - j q).$$
-/
theorem lagrangeSeriesCoefficient_of_ne_zero (p q n : ℝ) {k : ℕ} (hk : k ≠ 0) :
    lagrangeSeriesCoefficient p q n k =
      n * ∏ j ∈ Finset.range (k - 1),
        (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q) := by
  simp [lagrangeSeriesCoefficient, hk]

private noncomputable def ch3E14Coeff (p q n : ℝ) (k : ℕ) : ℝ :=
  lagrangeSeriesCoefficient p q n k / (Nat.factorial k : ℝ)

@[simp]
private theorem ch3E14Coeff_zero (p q n : ℝ) : ch3E14Coeff p q n 0 = 1 := by
  simp [ch3E14Coeff]

private theorem ch3E14Coeff_sub (p q y : ℝ) (k : ℕ) :
    ch3E14Coeff p q y (k + 1) - ch3E14Coeff p q (y - q) (k + 1) =
      q * ch3E14Coeff p q (y + p - q) k := by
  cases k with
  | zero =>
      simp [ch3E14Coeff, lagrangeSeriesCoefficient]
  | succ k =>
      have hprod₁ :
          ∏ j ∈ Finset.range (k + 1),
              (y + ((k + 2 : ℕ) : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q) =
            (y + ((k + 2 : ℕ) : ℝ) * p - q) *
              ∏ j ∈ Finset.range k,
                (y + ((k + 2 : ℕ) : ℝ) * p - ((j + 2 : ℕ) : ℝ) * q) := by
        rw [Finset.prod_range_succ']
        conv_lhs => rw [mul_comm]
        congr 1
        · push_cast
          ring
      have hprod₂ :
          ∏ j ∈ Finset.range (k + 1),
              (y - q + ((k + 2 : ℕ) : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q) =
            (∏ j ∈ Finset.range k,
                (y + ((k + 2 : ℕ) : ℝ) * p - ((j + 2 : ℕ) : ℝ) * q)) *
              (y + ((k + 2 : ℕ) : ℝ) * (p - q)) := by
        rw [Finset.prod_range_succ]
        congr 1
        · apply Finset.prod_congr rfl
          intro j _
          push_cast
          ring
        · push_cast
          ring
      rw [ch3E14Coeff, ch3E14Coeff,
        lagrangeSeriesCoefficient_of_ne_zero _ _ _ (Nat.succ_ne_zero _),
        lagrangeSeriesCoefficient_of_ne_zero _ _ _ (Nat.succ_ne_zero _)]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      rw [hprod₁, hprod₂, ch3E14Coeff,
        lagrangeSeriesCoefficient_of_ne_zero _ _ _ (Nat.succ_ne_zero _)]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
      ring_nf

private noncomputable def ch3E14Polynomial (p q : ℝ) (k : ℕ) : Polynomial ℝ :=
  if k = 0 then 1 else
    Polynomial.C ((Nat.factorial k : ℝ)⁻¹) * Polynomial.X *
      ∏ j ∈ Finset.range (k - 1),
        (Polynomial.X + Polynomial.C ((k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q))

private theorem ch3E14Polynomial_eval (p q n : ℝ) (k : ℕ) :
    Polynomial.eval n (ch3E14Polynomial p q k) = ch3E14Coeff p q n k := by
  by_cases hk : k = 0
  · subst k
    simp [ch3E14Polynomial]
  · simp only [ch3E14Polynomial, hk, ↓reduceIte]
    rw [ch3E14Coeff, lagrangeSeriesCoefficient_of_ne_zero p q n hk]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have hprod :
        (∏ j ∈ Finset.range (k - 1),
            (n + ((k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q))) =
          ∏ j ∈ Finset.range (k - 1),
            (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q) := by
      apply Finset.prod_congr rfl
      intro j _
      ring
    rw [hprod, div_eq_mul_inv]
    ring

private theorem ch3E14Coeff_zero_param (p q : ℝ) (k : ℕ) :
    ch3E14Coeff p q 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [ch3E14Coeff, lagrangeSeriesCoefficient_of_ne_zero p q 0 hk]
    simp [hk]

private theorem ch3E14Convolution_sub (p q r s : ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 2),
        ch3E14Coeff p q r k * ch3E14Coeff p q s (m + 1 - k)) -
      (∑ k ∈ Finset.range (m + 2),
        ch3E14Coeff p q (r - q) k * ch3E14Coeff p q s (m + 1 - k)) =
      q * ∑ k ∈ Finset.range (m + 1),
        ch3E14Coeff p q (r + p - q) k * ch3E14Coeff p q s (m - k) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [ch3E14Coeff_zero, one_mul, sub_self, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← sub_mul, ch3E14Coeff_sub]
  rw [Nat.add_sub_add_right]
  ring_nf

private theorem ch3E14Coeff_add_of_ne_zero (p q r s : ℝ) (hq : q ≠ 0) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1),
        ch3E14Coeff p q r k * ch3E14Coeff p q s (m - k)) =
      ch3E14Coeff p q (r + s) m := by
  induction m generalizing r s with
  | zero => simp
  | succ m ih =>
      let P : Polynomial ℝ := ∑ k ∈ Finset.range (m + 2),
        ch3E14Polynomial p q k * Polynomial.C (ch3E14Coeff p q s (m + 1 - k))
      let Q : Polynomial ℝ := (ch3E14Polynomial p q (m + 1)).comp
        (Polynomial.X + Polynomial.C s)
      have hevalP (t : ℝ) : Polynomial.eval t P =
          ∑ k ∈ Finset.range (m + 2),
            ch3E14Coeff p q t k * ch3E14Coeff p q s (m + 1 - k) := by
        dsimp only [P]
        rw [Polynomial.eval_finsetSum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Polynomial.eval_mul, Polynomial.eval_C, ch3E14Polynomial_eval]
      have hevalQ (t : ℝ) :
          Polynomial.eval t Q = ch3E14Coeff p q (t + s) (m + 1) := by
        dsimp only [Q]
        rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_C, ch3E14Polynomial_eval]
      have hzero : Polynomial.eval 0 P = Polynomial.eval 0 Q := by
        rw [hevalP, hevalQ]
        simp [ch3E14Coeff_zero_param]
      have hstep (t : ℝ) (ht : Polynomial.eval t P = Polynomial.eval t Q) :
          Polynomial.eval (t - q) P = Polynomial.eval (t - q) Q := by
        rw [hevalP, hevalQ] at ht ⊢
        have hF := ch3E14Convolution_sub p q t s m
        rw [ih (t + p - q) s] at hF
        have hG := ch3E14Coeff_sub p q (t + s) m
        have harg₁ : t + p - q + s = t + s + p - q := by ring
        have harg₂ : t + s - q = t - q + s := by ring
        rw [harg₁] at hF
        rw [harg₂] at hG
        linarith
      have hpoints : ∀ N : ℕ,
          Polynomial.eval (-((N : ℝ) * q)) P = Polynomial.eval (-((N : ℝ) * q)) Q := by
        intro N
        induction N with
        | zero => simpa using hzero
        | succ N hN =>
            convert hstep (-((N : ℝ) * q)) hN using 1 <;> push_cast <;> ring_nf
      have hinj : Function.Injective (fun N : ℕ => -((N : ℝ) * q)) := by
        intro M N hMN
        have hmul : (M : ℝ) * q = (N : ℝ) * q := by linarith
        have hcast : (M : ℝ) = (N : ℝ) := mul_right_cancel₀ hq hmul
        exact Nat.cast_injective hcast
      have hPQ : P = Q := Polynomial.eq_of_infinite_eval_eq P Q
        (Set.infinite_of_injective_forall_mem hinj hpoints)
      have h := congrArg (Polynomial.eval r) hPQ
      rw [hevalP, hevalQ] at h
      simpa only [Nat.succ_eq_add_one] using h

private theorem lagrangeSeriesCoefficient_add_zero (p r s : ℝ) (m : ℕ) :
    lagrangeSeriesCoefficient p 0 (r + s) m =
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) *
        lagrangeSeriesCoefficient p 0 r k * lagrangeSeriesCoefficient p 0 s (m - k) := by
  symm
  have h := Entry13CorollarySchroder.schroder_abel_binomial
    (p : ℂ) (r : ℂ) (s : ℂ) m
  let A (n : ℝ) (k : ℕ) : ℝ :=
    if k = 0 then 1 else n * (n + (k : ℝ) * p) ^ (k - 1)
  have hcoeff (n : ℝ) (k : ℕ) : lagrangeSeriesCoefficient p 0 n k = A n k := by
    simp [A, lagrangeSeriesCoefficient, Finset.prod_const]
  have hcast (n : ℝ) (k : ℕ) :
      (A n k : ℂ) =
        if k = 0 then 1 else (n : ℂ) * ((n : ℂ) + (k : ℂ) * (p : ℂ)) ^ (k - 1) := by
    by_cases hk : k = 0 <;> simp [A, hk]
  simp only [hcoeff]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [hcast]
  push_cast
  exact h

/-- **Hagen–Rothe convolution for Lagrange series coefficients.** For all real numbers $p$, $q$,
$r$, $s$ and every natural number $m$, the Lagrange series coefficients $C_{p,q}$ satisfy
$$C_{p,q}(r + s, m) = \sum_{k=0}^{m} \binom{m}{k} C_{p,q}(r, k) \, C_{p,q}(s, m - k).$$
-/
theorem lagrangeSeriesCoefficient_add (p q r s : ℝ) (m : ℕ) :
    lagrangeSeriesCoefficient p q (r + s) m =
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) *
        lagrangeSeriesCoefficient p q r k * lagrangeSeriesCoefficient p q s (m - k) := by
  by_cases hq : q = 0
  · subst q
    exact lagrangeSeriesCoefficient_add_zero p r s m
  have h := ch3E14Coeff_add_of_ne_zero p q r s hq m
  calc
    lagrangeSeriesCoefficient p q (r + s) m =
        (Nat.factorial m : ℝ) * ch3E14Coeff p q (r + s) m := by
          rw [ch3E14Coeff]
          field_simp
    _ = (Nat.factorial m : ℝ) *
        ∑ k ∈ Finset.range (m + 1),
          ch3E14Coeff p q r k * ch3E14Coeff p q s (m - k) := by rw [h]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hfactorial :
          (Nat.choose m k : ℝ) * (Nat.factorial k : ℝ) *
              (Nat.factorial (m - k) : ℝ) = (Nat.factorial m : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
      rw [ch3E14Coeff, ch3E14Coeff, ← hfactorial]
      field_simp

private theorem ch3E14Coeff_add (p q r s : ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1),
        ch3E14Coeff p q r k * ch3E14Coeff p q s (m - k)) =
      ch3E14Coeff p q (r + s) m := by
  have h := lagrangeSeriesCoefficient_add p q r s m
  calc
    (∑ k ∈ Finset.range (m + 1),
        ch3E14Coeff p q r k * ch3E14Coeff p q s (m - k)) =
        (∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) *
          lagrangeSeriesCoefficient p q r k *
          lagrangeSeriesCoefficient p q s (m - k)) / (Nat.factorial m : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hfactorial :
          (Nat.choose m k : ℝ) * (Nat.factorial k : ℝ) *
              (Nat.factorial (m - k) : ℝ) = (Nat.factorial m : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
      have hchoose : (Nat.choose m k : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos hkm).ne'
      rw [ch3E14Coeff, ch3E14Coeff, ← hfactorial]
      field_simp [hchoose]
    _ = lagrangeSeriesCoefficient p q (r + s) m / (Nat.factorial m : ℝ) := by
      rw [h]
    _ = ch3E14Coeff p q (r + s) m := rfl

private theorem ch3E14_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.factorial n : ℝ) ≤ Real.exp 1 *
      (Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n) := by
  have hmono : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    have h := Stirling.stirlingSeq'_antitone (Nat.zero_le (n - 1))
    simpa [Function.comp_apply, Nat.sub_add_cancel hn] using h
  rw [Stirling.stirlingSeq, Stirling.stirlingSeq_one] at hmono
  have hden : 0 < Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n := by positivity
  rw [div_le_iff₀ hden] at hmono
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hconst : Real.exp 1 / Real.sqrt 2 ≤ Real.exp 1 := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
    nlinarith [Real.exp_pos 1]
  exact hmono.trans (mul_le_mul_of_nonneg_right hconst hden.le)

private theorem ch3E14_Gamma_le_interpolate (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : 0 < x) (hx₁ : x ≤ 1) :
    Real.Gamma ((n : ℝ) + x) ≤
      (Nat.factorial (n - 1) : ℝ) * (n : ℝ) ^ x := by
  have hfeq : ∀ {y : ℝ}, 0 < y →
      (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
    intro y hy
    simp only [Function.comp_apply]
    rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    ac_rfl
  have hlog := Real.BohrMollerup.f_add_nat_le Real.convexOn_log_Gamma hfeq
    (Nat.ne_of_gt hn) hx hx₁
  have hGammaNat : Real.Gamma (n : ℝ) = (Nat.factorial (n - 1) : ℝ) := by
    have hn_eq : n - 1 + 1 = n := by omega
    calc
      Real.Gamma (n : ℝ) = Real.Gamma ((n - 1 : ℕ) + 1) := by
        congr 1
        exact_mod_cast hn_eq.symm
      _ = (Nat.factorial (n - 1) : ℝ) := Real.Gamma_nat_eq_factorial (n - 1)
  rw [Function.comp_apply, Function.comp_apply, hGammaNat] at hlog
  calc
    Real.Gamma ((n : ℝ) + x) = Real.exp (Real.log (Real.Gamma ((n : ℝ) + x))) :=
      (Real.exp_log (Real.Gamma_pos_of_pos (by positivity))).symm
    _ ≤ Real.exp (Real.log (Nat.factorial (n - 1) : ℝ) + x * Real.log n) :=
      Real.exp_le_exp.mpr hlog
    _ = (Nat.factorial (n - 1) : ℝ) * (n : ℝ) ^ x := by
      rw [Real.exp_add, Real.exp_log (by positivity), Real.rpow_def_of_pos (by positivity)]
      congr 1
      ring_nf

private theorem ch3E14_Gamma_le (y : ℝ) (hy : 3 ≤ y) :
    Real.Gamma y ≤ Real.exp 2 *
      (Real.sqrt (2 * y) * (y / Real.exp 1) ^ (y - 1)) := by
  let c : ℕ := ⌈y⌉₊
  let n : ℕ := c - 1
  let x : ℝ := y - n
  have hy0 : 0 ≤ y := by linarith
  have hyc : y ≤ (c : ℝ) := by
    simpa only [c] using Nat.le_ceil y
  have hc_lt : (c : ℝ) < y + 1 := by
    simpa only [c] using Nat.ceil_lt_add_one hy0
  have hc3 : 3 ≤ c := by
    exact_mod_cast hy.trans hyc
  have hn2 : 2 ≤ n := by simp only [n]; omega
  have hnc : n + 1 = c := by simp only [n]; omega
  have hn_lt : (n : ℝ) < y := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hnc] at hcast
    linarith
  have hy_le : y ≤ (n : ℝ) + 1 := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hnc] at hcast
    linarith
  have hx0 : 0 < x := by simp only [x]; linarith
  have hx1 : x ≤ 1 := by simp only [x]; linarith
  have hny : (n : ℝ) ≤ y := hn_lt.le
  have hnm1y : ((n - 1 : ℕ) : ℝ) ≤ y := by
    exact (Nat.cast_le.mpr (Nat.sub_le n 1)).trans hny
  have hbase : ((n - 1 : ℕ) : ℝ) / Real.exp 1 ≤ y / Real.exp 1 := by
    exact div_le_div_of_nonneg_right hnm1y (Real.exp_pos 1).le
  have hpow : (((n - 1 : ℕ) : ℝ) / Real.exp 1) ^ (n - 1) ≤
      (y / Real.exp 1) ^ (n - 1) := by
    exact pow_le_pow_left₀ (by positivity) hbase (n - 1)
  have hsqrt : Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * y) := by
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hnx : (n : ℝ) ^ x ≤ y ^ x := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) hny hx0.le
  have hfac := ch3E14_factorial_le (n - 1) (by omega)
  have hinterp := ch3E14_Gamma_le_interpolate n x (by omega) hx0 hx1
  have harg : (n : ℝ) + x = y := by simp only [x]; ring
  rw [harg] at hinterp
  calc
    Real.Gamma y ≤ (Nat.factorial (n - 1) : ℝ) * (n : ℝ) ^ x := hinterp
    _ ≤ (Real.exp 1 *
        (Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)) *
          (((n - 1 : ℕ) : ℝ) / Real.exp 1) ^ (n - 1))) * (n : ℝ) ^ x := by
      gcongr
    _ ≤ (Real.exp 1 *
        (Real.sqrt (2 * y) * (y / Real.exp 1) ^ (n - 1))) * y ^ x := by
      gcongr
    _ ≤ Real.exp 2 *
        (Real.sqrt (2 * y) * (y / Real.exp 1) ^ (y - 1)) := by
      rw [← Real.rpow_natCast]
      have hypos : 0 < y := by linarith
      have hquot : 0 < y / Real.exp 1 := div_pos hypos (Real.exp_pos 1)
      have hexpx : (Real.exp 1) ^ x ≤ Real.exp 1 := by
        rw [← Real.exp_mul]
        simpa using Real.exp_le_exp.mpr hx1
      have hyfactor : y ^ x = (y / Real.exp 1) ^ x * (Real.exp 1) ^ x := by
        rw [← Real.mul_rpow (le_of_lt hquot) (Real.exp_pos 1).le]
        congr 1
        field_simp
      rw [hyfactor]
      have hcombine : (y / Real.exp 1) ^ ((n - 1 : ℕ) : ℝ) *
          (y / Real.exp 1) ^ x =
            (y / Real.exp 1) ^ (((n - 1 : ℕ) : ℝ) + x) := by
        rw [Real.rpow_add hquot]
      have hrearrange :
          Real.exp 1 *
              (Real.sqrt (2 * y) * (y / Real.exp 1) ^ ((n - 1 : ℕ) : ℝ)) *
                ((y / Real.exp 1) ^ x * (Real.exp 1) ^ x) =
            Real.exp 1 * (Real.exp 1) ^ x *
              (Real.sqrt (2 * y) *
                (y / Real.exp 1) ^ (((n - 1 : ℕ) : ℝ) + x)) := by
        rw [← hcombine]
        ring
      rw [hrearrange]
      have hexp : ((n - 1 : ℕ) : ℝ) + x = y - 1 := by
        simp only [x]
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hexp, show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      gcongr

private theorem ch3E14_inv_Gamma_add_one (s : ℝ) :
    (Real.Gamma s)⁻¹ = s * (Real.Gamma (s + 1))⁻¹ := by
  by_cases hs : s = 0
  · subst s
    simp [Real.Gamma_zero]
  · rw [Real.Gamma_add_one hs, mul_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

private theorem ch3E14_inv_Gamma_sub_nat (x : ℝ) (m : ℕ) :
    (Real.Gamma (x - m))⁻¹ =
      (∏ j ∈ Finset.range m, (x - ((j + 1 : ℕ) : ℝ))) * (Real.Gamma x)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [ch3E14_inv_Gamma_add_one (x - (m + 1 : ℕ))]
      have harg : x - ((m + 1 : ℕ) : ℝ) + 1 = x - (m : ℝ) := by
        push_cast
        ring
      rw [harg, ih, Finset.prod_range_succ]
      push_cast
      ring

private theorem ch3E14_inv_Gamma_reflection {s : ℝ} (hs : s < 1) :
    (Real.Gamma s)⁻¹ =
      Real.Gamma (1 - s) * Real.sin (Real.pi * s) / Real.pi := by
  by_cases hzero : Real.Gamma s = 0
  · rw [hzero, inv_zero]
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff s).mp hzero
    subst s
    rw [show Real.pi * (-(m : ℝ)) = -((m : ℝ) * Real.pi) by ring,
      Real.sin_neg, Real.sin_nat_mul_pi]
    ring
  · have hone : 0 < 1 - s := sub_pos.mpr hs
    have hreflect := Real.Gamma_mul_Gamma_one_sub s
    have hsin : Real.sin (Real.pi * s) ≠ 0 := by
      intro h
      rw [h, div_zero] at hreflect
      exact (mul_ne_zero hzero (Real.Gamma_pos_of_pos hone).ne') hreflect
    have hreflect' :
        Real.Gamma s * Real.Gamma (1 - s) * Real.sin (Real.pi * s) = Real.pi := by
      simpa [mul_comm] using (eq_div_iff hsin).mp hreflect
    apply (eq_div_iff Real.pi_ne_zero).mpr
    calc
      (Real.Gamma s)⁻¹ * Real.pi =
          (Real.Gamma s)⁻¹ *
            (Real.Gamma s * Real.Gamma (1 - s) * Real.sin (Real.pi * s)) := by
              rw [hreflect']
      _ = Real.Gamma (1 - s) * Real.sin (Real.pi * s) := by field_simp [hzero]

private theorem ch3E14_abs_inv_Gamma_le {s : ℝ} (hs : s < 1) :
    |(Real.Gamma s)⁻¹| ≤ Real.Gamma (1 - s) := by
  rw [ch3E14_inv_Gamma_reflection hs, abs_div, abs_mul,
    abs_of_pos (Real.Gamma_pos_of_pos (sub_pos.mpr hs)), abs_of_pos Real.pi_pos]
  have hsin := Real.abs_sin_le_one (Real.pi * s)
  have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  calc
    Real.Gamma (1 - s) * |Real.sin (Real.pi * s)| / Real.pi ≤
        Real.Gamma (1 - s) * 1 / Real.pi := by gcongr
    _ ≤ Real.Gamma (1 - s) := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.Gamma_pos_of_pos (sub_pos.mpr hs)]

private theorem ch3E14_abs_prod_le_Gamma (x : ℝ) (k : ℕ)
    (hx : 0 < x) (hxk : x < k) :
    |∏ j ∈ Finset.range (k - 1), (x - ((j + 1 : ℕ) : ℝ))| ≤
      Real.Gamma x * Real.Gamma ((k : ℝ) - x) := by
  have hk : 1 ≤ k := by
    have : (0 : ℝ) < k := hx.trans hxk
    exact_mod_cast this
  have hrec := ch3E14_inv_Gamma_sub_nat x (k - 1)
  have harg : x - ((k - 1 : ℕ) : ℝ) = x - k + 1 := by
    rw [Nat.cast_sub hk]
    push_cast
    ring
  rw [harg] at hrec
  have hGamma : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have hprod :
      (∏ j ∈ Finset.range (k - 1), (x - ((j + 1 : ℕ) : ℝ))) =
        Real.Gamma x * (Real.Gamma (x - k + 1))⁻¹ := by
    apply (mul_right_cancel₀ hGamma)
    rw [hrec]
    field_simp
  rw [hprod, abs_mul, abs_of_pos (Real.Gamma_pos_of_pos hx)]
  have hs : x - k + 1 < 1 := by linarith
  have hinv := ch3E14_abs_inv_Gamma_le hs
  have hsame : 1 - (x - k + 1) = (k : ℝ) - x := by ring
  rw [hsame] at hinv
  exact mul_le_mul_of_nonneg_left hinv (Real.Gamma_pos_of_pos hx).le

private theorem ch3E14_shift_ratio_le (u v B : ℝ) (hv : 0 < v) (hB : 0 ≤ B)
    (hu_upper : u ≤ v + B) (hBv : B ≤ v)
    (hu_one : 1 ≤ u) :
    (u / v) ^ (u - 1) ≤ Real.exp (2 * B) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu_one
  have hratio0 : 0 ≤ u / v := (div_pos hu0 hv).le
  have hratio : u / v ≤ Real.exp (B / v) := by
    calc
      u / v ≤ (v + B) / v := div_le_div_of_nonneg_right hu_upper hv.le
      _ = 1 + B / v := by field_simp
      _ ≤ Real.exp (B / v) := by simpa [add_comm] using Real.add_one_le_exp (B / v)
  calc
    (u / v) ^ (u - 1) ≤ (Real.exp (B / v)) ^ (u - 1) :=
      Real.rpow_le_rpow hratio0 hratio (sub_nonneg.mpr hu_one)
    _ = Real.exp ((B / v) * (u - 1)) := (Real.exp_mul _ _).symm
    _ ≤ Real.exp (2 * B) := by
      apply Real.exp_le_exp.mpr
      have hu_two : u ≤ 2 * v := by nlinarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hv]
      nlinarith

private theorem ch3E14_shifted_entropy_le (α b β B : ℝ) (k : ℕ)
    (hα : 0 < α) (hb : 0 < b) (hαb : α + b = 1) (hB : 0 ≤ B)
    (hβ : |β| ≤ B) (hkα : B + 1 ≤ α * k) (hkb : B + 1 ≤ b * k) :
    (((α * k + β) / Real.exp 1) ^ (α * k + β - 1) *
        ((b * k - β) / Real.exp 1) ^ (b * k - β - 1)) *
          (α ^ (-α) * b ^ (-b)) ^ k ≤
      (Real.exp (4 * B) * α ^ (-B - 1) * b ^ (-B - 1)) *
        ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 2) := by
  let K : ℝ := k
  let X : ℝ := α * K + β
  let Y : ℝ := b * K - β
  have hβbounds : -B ≤ β ∧ β ≤ B := (abs_le.mp hβ)
  have hK : 0 < K := by
    have : 0 < α * K := by
      simp only [K] at hkα ⊢
      nlinarith
    exact pos_of_mul_pos_right this hα.le
  have hαK : 0 < α * K := mul_pos hα hK
  have hbK : 0 < b * K := mul_pos hb hK
  have hX1 : 1 ≤ X := by simp only [X]; nlinarith
  have hY1 : 1 ≤ Y := by simp only [Y]; nlinarith
  have hXupper : X ≤ α * K + B := by simp only [X]; linarith
  have hYupper : Y ≤ b * K + B := by simp only [Y]; linarith
  have hBKα : B ≤ α * K := by simp only [K] at hkα ⊢; linarith
  have hBKb : B ≤ b * K := by simp only [K] at hkb ⊢; linarith
  have hratioX := ch3E14_shift_ratio_le X (α * K) B hαK hB hXupper hBKα hX1
  have hratioY := ch3E14_shift_ratio_le Y (b * K) B hbK hB hYupper hBKb hY1
  have hratios :
      (X / (α * K)) ^ (X - 1) * (Y / (b * K)) ^ (Y - 1) ≤ Real.exp (4 * B) := by
    calc
      (X / (α * K)) ^ (X - 1) * (Y / (b * K)) ^ (Y - 1) ≤
          Real.exp (2 * B) * Real.exp (2 * B) :=
        mul_le_mul hratioX hratioY
          (Real.rpow_nonneg (div_nonneg (zero_lt_one.trans_le hY1).le hbK.le) _)
          (Real.exp_pos _).le
      _ = Real.exp (4 * B) := by rw [← Real.exp_add]; congr 1; ring
  have hαle : α ≤ 1 := by nlinarith
  have hble : b ≤ 1 := by nlinarith
  have hshiftα : α ^ (β - 1) ≤ α ^ (-B - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hα hαle (by linarith)
  have hshiftb : b ^ (-β - 1) ≤ b ^ (-B - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hb hble (by linarith)
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hYpos : 0 < Y := zero_lt_one.trans_le hY1
  have hKE : 0 < K / Real.exp 1 := div_pos hK (Real.exp_pos 1)
  have hXsplit :
      (X / Real.exp 1) ^ (X - 1) =
        α ^ (X - 1) * (K / Real.exp 1) ^ (X - 1) *
          (X / (α * K)) ^ (X - 1) := by
    have hbase : X / Real.exp 1 = (α * (K / Real.exp 1)) * (X / (α * K)) := by
      field_simp
    rw [hbase, Real.mul_rpow (mul_nonneg hα.le hKE.le)
      (div_nonneg hXpos.le hαK.le), Real.mul_rpow hα.le hKE.le]
  have hYsplit :
      (Y / Real.exp 1) ^ (Y - 1) =
        b ^ (Y - 1) * (K / Real.exp 1) ^ (Y - 1) *
          (Y / (b * K)) ^ (Y - 1) := by
    have hbase : Y / Real.exp 1 = (b * (K / Real.exp 1)) * (Y / (b * K)) := by
      field_simp
    rw [hbase, Real.mul_rpow (mul_nonneg hb.le hKE.le)
      (div_nonneg hYpos.le hbK.le), Real.mul_rpow hb.le hKE.le]
  have hcritical : (α ^ (-α) * b ^ (-b)) ^ k =
      α ^ (-α * K) * b ^ (-b * K) := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hα.le, ← Real.rpow_mul hb.le]
  have hXexp : X - 1 + -α * K = β - 1 := by simp only [X]; ring
  have hYexp : Y - 1 + -b * K = -β - 1 := by simp only [Y]; ring
  have hKexp : X - 1 + (Y - 1) = K - 2 := by
    simp only [X, Y]
    nlinarith
  have hαcombine : α ^ (X - 1) * α ^ (-α * K) = α ^ (β - 1) := by
    rw [← Real.rpow_add hα, hXexp]
  have hbcombine : b ^ (Y - 1) * b ^ (-b * K) = b ^ (-β - 1) := by
    rw [← Real.rpow_add hb, hYexp]
  have hKcombine : (K / Real.exp 1) ^ (X - 1) *
      (K / Real.exp 1) ^ (Y - 1) = (K / Real.exp 1) ^ (K - 2) := by
    rw [← Real.rpow_add hKE, hKexp]
  have hshifts : α ^ (β - 1) * b ^ (-β - 1) ≤
      α ^ (-B - 1) * b ^ (-B - 1) :=
    mul_le_mul hshiftα hshiftb (Real.rpow_nonneg hb.le _)
      (Real.rpow_nonneg hα.le _)
  rw [show (α * (k : ℝ) + β) = X by rfl,
    show (b * (k : ℝ) - β) = Y by rfl, hXsplit, hYsplit, hcritical]
  calc
    ((α ^ (X - 1) * (K / Real.exp 1) ^ (X - 1) * (X / (α * K)) ^ (X - 1)) *
          (b ^ (Y - 1) * (K / Real.exp 1) ^ (Y - 1) * (Y / (b * K)) ^ (Y - 1))) *
        (α ^ (-α * K) * b ^ (-b * K)) =
      ((X / (α * K)) ^ (X - 1) * (Y / (b * K)) ^ (Y - 1)) *
        (α ^ (β - 1) * b ^ (-β - 1)) *
          (K / Real.exp 1) ^ (K - 2) := by
            rw [← hαcombine, ← hbcombine, ← hKcombine]
            ring
    _ ≤ (Real.exp (4 * B) * α ^ (-B - 1) * b ^ (-B - 1)) *
        (K / Real.exp 1) ^ (K - 2) := by
      have hshift0 : 0 ≤ α ^ (β - 1) * b ^ (-β - 1) := by positivity
      have hpair :
          ((X / (α * K)) ^ (X - 1) * (Y / (b * K)) ^ (Y - 1)) *
              (α ^ (β - 1) * b ^ (-β - 1)) ≤
            Real.exp (4 * B) * (α ^ (-B - 1) * b ^ (-B - 1)) :=
        mul_le_mul hratios hshifts hshift0 (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right (by nlinarith [hpair]) (Real.rpow_nonneg hKE.le _)

private theorem ch3E14_radius_mul_q_of_lt (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p < q) :
    (p ^ (-p / q) * |p - q| ^ ((p - q) / q)) * q =
      (p / q) ^ (-(p / q)) * ((q - p) / q) ^ (-((q - p) / q)) := by
  let α : ℝ := p / q
  let b : ℝ := (q - p) / q
  have hα : 0 < α := by simp only [α]; positivity
  have hb : 0 < b := by simp only [b]; positivity
  have hαb : α + b = 1 := by simp only [α, b]; field_simp; ring
  have hpbase : p = q * α := by simp only [α]; field_simp
  have hbbase : q - p = q * b := by simp only [b]; field_simp
  have hnegp : -p / q = -α := by simp only [α]; ring
  have hdiff : (p - q) / q = -b := by simp only [b]; field_simp; ring
  have habs : |p - q| = q - p := by rw [abs_of_neg (sub_neg.mpr hpq)]; ring
  rw [hnegp, hdiff]
  change (p ^ (-α) * |p - q| ^ (-b)) * q = α ^ (-α) * b ^ (-b)
  rw [habs, hbbase, hpbase,
    Real.mul_rpow hq.le hα.le, Real.mul_rpow hq.le hb.le]
  have hzero : (1 : ℝ) + -α + -b = 0 := by linarith
  calc
    (q ^ (-α) * α ^ (-α) * (q ^ (-b) * b ^ (-b))) * q =
        (q ^ (1 : ℝ) * q ^ (-α) * q ^ (-b)) * (α ^ (-α) * b ^ (-b)) := by
          rw [Real.rpow_one]
          ring
    _ = q ^ ((1 : ℝ) + -α + -b) * (α ^ (-α) * b ^ (-b)) := by
      rw [Real.rpow_add hq, Real.rpow_add hq]
    _ = _ := by rw [hzero, Real.rpow_zero, one_mul]

private theorem ch3E14_product_scale (p q n : ℝ) (k : ℕ) (hq : q ≠ 0) :
    (∏ j ∈ Finset.range (k - 1),
        (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)) =
      q ^ (k - 1) *
        ∏ j ∈ Finset.range (k - 1),
          ((n + (k : ℝ) * p) / q - ((j + 1 : ℕ) : ℝ)) := by
  calc
    (∏ j ∈ Finset.range (k - 1),
        (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)) =
      ∏ j ∈ Finset.range (k - 1),
        q * ((n + (k : ℝ) * p) / q - ((j + 1 : ℕ) : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j _
          field_simp
    _ = (∏ _j ∈ Finset.range (k - 1), q) *
        ∏ j ∈ Finset.range (k - 1),
          ((n + (k : ℝ) * p) / q - ((j + 1 : ℕ) : ℝ)) :=
      Finset.prod_mul_distrib
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

private theorem ch3E14_stirling_ratio_le (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) * ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 2)) /
        (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ (k : ℝ)) ≤
      Real.exp 2 * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
  let K : ℝ := k
  let t : ℝ := K / Real.exp 1
  have hK : 0 < K := by
    simp only [K]
    exact_mod_cast (Nat.zero_lt_of_lt hk)
  have ht : 0 < t := div_pos hK (Real.exp_pos 1)
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hsqrt : Real.sqrt K ≤ Real.sqrt (2 * Real.pi * K) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.two_le_pi]
  have hpowquot : t ^ (K - 2) / t ^ K = t ^ (-2 : ℝ) := by
    rw [← Real.rpow_sub ht]
    congr 1
    ring
  have htneg : t ^ (-2 : ℝ) = (Real.exp 1) ^ 2 / K ^ 2 := by
    rw [Real.rpow_neg ht.le]
    have ht2 : t ^ (2 : ℝ) = t ^ (2 : ℕ) := Real.rpow_natCast t 2
    rw [ht2]
    simp only [t]
    field_simp
  have hexp2 : (Real.exp 1) ^ (2 : ℕ) = Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hKpow : K ^ (-(3 / 2 : ℝ)) = (K * Real.sqrt K)⁻¹ := by
    have hexponent : -(3 / 2 : ℝ) = -(1 + 1 / 2) := by norm_num
    rw [hexponent, Real.rpow_neg hK.le, Real.rpow_add hK, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  change (K * t ^ (K - 2)) / (Real.sqrt (2 * Real.pi * K) * t ^ K) ≤
    Real.exp 2 * K ^ (-(3 / 2 : ℝ))
  have hrearrange :
      (K * t ^ (K - 2)) / (Real.sqrt (2 * Real.pi * K) * t ^ K) =
        (K / Real.sqrt (2 * Real.pi * K)) * (t ^ (K - 2) / t ^ K) := by
    field_simp
  rw [hrearrange, hpowquot, htneg, hexp2, hKpow]
  have hleft :
      K / Real.sqrt (2 * Real.pi * K) * (Real.exp 2 / K ^ 2) =
        Real.exp 2 / (K * Real.sqrt (2 * Real.pi * K)) := by
    field_simp
  have hright : Real.exp 2 * (K * Real.sqrt K)⁻¹ =
      Real.exp 2 / (K * Real.sqrt K) := by rw [div_eq_mul_inv]
  rw [hleft, hright]
  exact div_le_div_of_nonneg_left (Real.exp_pos 2).le (mul_pos hK hsqrtK)
    (mul_le_mul_of_nonneg_left hsqrt hK.le)

set_option maxHeartbeats 800000 in
-- This estimate combines several nonlinear real-power inequalities.
private theorem ch3E14_coeff_radius_le_of_lt (p q N n : ℝ) (k : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p < q) (hN : 0 ≤ N) (hn : |n| ≤ N)
    (hkα : N / q + 3 ≤ (p / q) * k)
    (hkb : N / q + 3 ≤ ((q - p) / q) * k) :
    |ch3E14Coeff p q n k| *
        (p ^ (-p / q) * |p - q| ^ ((p - q) / q)) ^ k ≤
      ((N / q) * Real.exp 4 * 2 *
          (Real.exp (4 * (N / q)) * (p / q) ^ (-(N / q) - 1) *
            ((q - p) / q) ^ (-(N / q) - 1)) * Real.exp 2) *
        (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
  let α : ℝ := p / q
  let b : ℝ := (q - p) / q
  let B : ℝ := N / q
  let β : ℝ := n / q
  let X : ℝ := α * k + β
  let Y : ℝ := b * k - β
  let R : ℝ := p ^ (-p / q) * |p - q| ^ ((p - q) / q)
  let C₀ : ℝ := Real.exp (4 * B) * α ^ (-B - 1) * b ^ (-B - 1)
  have hα : 0 < α := by simp only [α]; positivity
  have hb : 0 < b := by simp only [b]; positivity
  have hαb : α + b = 1 := by simp only [α, b]; field_simp; ring
  have hB : 0 ≤ B := by simp only [B]; positivity
  have hβ : |β| ≤ B := by
    simp only [β, B, abs_div, abs_of_pos hq]
    exact div_le_div_of_nonneg_right hn hq.le
  have hkα' : B + 3 ≤ α * k := by simpa only [B, α] using hkα
  have hkb' : B + 3 ≤ b * k := by simpa only [B, b] using hkb
  have hβbounds : -B ≤ β ∧ β ≤ B := abs_le.mp hβ
  have hX3 : 3 ≤ X := by simp only [X]; linarith
  have hY3 : 3 ≤ Y := by simp only [Y]; linarith
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := by linarith
  have hXY : X + Y = k := by simp only [X, Y]; nlinarith
  have hXk : X < k := by linarith
  have hYk : Y < k := by linarith
  have hk : 1 ≤ k := by
    have : (0 : ℝ) < k := hXpos.trans hXk
    exact_mod_cast this
  have hxeq : (n + (k : ℝ) * p) / q = X := by
    simp only [X, α, β]
    field_simp
    ring
  have hprodscale := ch3E14_product_scale p q n k hq.ne'
  rw [hxeq] at hprodscale
  let P : ℝ := ∏ j ∈ Finset.range (k - 1),
    (X - ((j + 1 : ℕ) : ℝ))
  have hprodscale' :
      (∏ j ∈ Finset.range (k - 1),
          (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)) = q ^ (k - 1) * P := by
    simpa only [P] using hprodscale
  have hqpow : q ^ k = q ^ (k - 1) * q := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  have hradius : R * q = α ^ (-α) * b ^ (-b) := by
    simpa only [R, α, b] using ch3E14_radius_mul_q_of_lt p q hp hq hpq
  have hRqpow : R ^ k * q ^ k = (α ^ (-α) * b ^ (-b)) ^ k := by
    rw [← mul_pow, hradius]
  have hRq : q ^ (k - 1) * R ^ k * q = (α ^ (-α) * b ^ (-b)) ^ k := by
    calc
      q ^ (k - 1) * R ^ k * q = R ^ k * (q ^ (k - 1) * q) := by ring
      _ = R ^ k * q ^ k := by rw [← hqpow]
      _ = _ := hRqpow
  have hcoeff :
      |ch3E14Coeff p q n k| * R ^ k =
        (|n| / q) * (|P| / (Nat.factorial k : ℝ)) *
          (α ^ (-α) * b ^ (-b)) ^ k := by
    have hfactabs : |(Nat.factorial k : ℝ)| = (Nat.factorial k : ℝ) :=
      abs_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos k))
    rw [ch3E14Coeff, lagrangeSeriesCoefficient_of_ne_zero p q n (Nat.ne_of_gt hk),
      hprodscale']
    simp only [abs_div, abs_mul, hfactabs, abs_pow, abs_of_pos hq]
    field_simp
    calc
      |n| * q ^ (k - 1) * |P| * R ^ k * q =
          |n| * |P| * (q ^ (k - 1) * R ^ k * q) := by ring
      _ = |n| * |P| * (α ^ (-α) * b ^ (-b)) ^ k := by rw [hRq]
  have hprod : |P| ≤ Real.Gamma X * Real.Gamma Y := by
    have hYeq : (k : ℝ) - X = Y := by linarith
    simpa only [P, hYeq] using ch3E14_abs_prod_le_Gamma X k hXpos hXk
  have hGX := ch3E14_Gamma_le X hX3
  have hGY := ch3E14_Gamma_le Y hY3
  have hGammas : Real.Gamma X * Real.Gamma Y ≤
      Real.exp 4 *
        ((Real.sqrt (2 * X) * Real.sqrt (2 * Y)) *
          (((X / Real.exp 1) ^ (X - 1)) * ((Y / Real.exp 1) ^ (Y - 1)))) := by
    calc
      Real.Gamma X * Real.Gamma Y ≤
          (Real.exp 2 * (Real.sqrt (2 * X) * (X / Real.exp 1) ^ (X - 1))) *
            (Real.exp 2 * (Real.sqrt (2 * Y) * (Y / Real.exp 1) ^ (Y - 1))) :=
        mul_le_mul hGX hGY (Real.Gamma_pos_of_pos hYpos).le
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.sqrt_nonneg _)
            (Real.rpow_nonneg (by positivity) _)))
      _ = _ := by
        rw [show Real.exp 4 = Real.exp 2 * Real.exp 2 by rw [← Real.exp_add]; norm_num]
        ring
  have hsqrt : Real.sqrt (2 * X) * Real.sqrt (2 * Y) ≤ 2 * (k : ℝ) := by
    have hXle : X ≤ (k : ℝ) := hXk.le
    have hYle : Y ≤ (k : ℝ) := hYk.le
    have hsX : Real.sqrt (2 * X) ≤ Real.sqrt (2 * k) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hsY : Real.sqrt (2 * Y) ≤ Real.sqrt (2 * k) :=
      Real.sqrt_le_sqrt (by nlinarith)
    calc
      Real.sqrt (2 * X) * Real.sqrt (2 * Y) ≤
          Real.sqrt (2 * k) * Real.sqrt (2 * k) :=
        mul_le_mul hsX hsY (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = 2 * (k : ℝ) := by rw [Real.mul_self_sqrt (by positivity)]
  have hentropy :
      ((X / Real.exp 1) ^ (X - 1) * (Y / Real.exp 1) ^ (Y - 1)) *
          (α ^ (-α) * b ^ (-b)) ^ k ≤
        C₀ * ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 2) := by
    simpa only [X, Y, C₀] using ch3E14_shifted_entropy_le α b β B k hα hb hαb hB hβ
      (by linarith) (by linarith)
  let D : ℝ := Real.sqrt (2 * Real.pi * k) *
    ((k : ℝ) / Real.exp 1) ^ k
  have hDpos : 0 < D := by simp only [D]; positivity
  have hfactorial : D ≤ (Nat.factorial k : ℝ) := by
    simpa only [D] using Stirling.le_factorial_stirling k
  have hratio := ch3E14_stirling_ratio_le k hk
  have hNq : 0 ≤ N / q := div_nonneg hN hq.le
  have hC₀ : 0 ≤ C₀ := by simp only [C₀]; positivity
  rw [show p ^ (-p / q) * |p - q| ^ ((p - q) / q) = R by rfl,
    show p / q = α by rfl, show (q - p) / q = b by rfl,
    show N / q = B by rfl]
  rw [hcoeff]
  calc
    (|n| / q) * (|P| / (Nat.factorial k : ℝ)) *
        (α ^ (-α) * b ^ (-b)) ^ k ≤
      (N / q) * ((Real.Gamma X * Real.Gamma Y) / (Nat.factorial k : ℝ)) *
        (α ^ (-α) * b ^ (-b)) ^ k := by
          gcongr
    _ ≤ (N / q) *
        ((Real.exp 4 * ((Real.sqrt (2 * X) * Real.sqrt (2 * Y)) *
          ((X / Real.exp 1) ^ (X - 1) * (Y / Real.exp 1) ^ (Y - 1)))) / D) *
            (α ^ (-α) * b ^ (-b)) ^ k := by
      have hdiv : (Real.Gamma X * Real.Gamma Y) / (Nat.factorial k : ℝ) ≤
          (Real.exp 4 * ((Real.sqrt (2 * X) * Real.sqrt (2 * Y)) *
            ((X / Real.exp 1) ^ (X - 1) * (Y / Real.exp 1) ^ (Y - 1)))) / D := by
        calc
          (Real.Gamma X * Real.Gamma Y) / (Nat.factorial k : ℝ) ≤
              (Real.exp 4 * ((Real.sqrt (2 * X) * Real.sqrt (2 * Y)) *
                ((X / Real.exp 1) ^ (X - 1) * (Y / Real.exp 1) ^ (Y - 1)))) /
                  (Nat.factorial k : ℝ) :=
            div_le_div_of_nonneg_right hGammas (Nat.cast_nonneg _)
          _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hDpos hfactorial
      gcongr
    _ ≤ (N / q) * (Real.exp 4 * (2 * (k : ℝ)) *
        (C₀ * ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 2)) / D) := by
      have hboth :
          (Real.sqrt (2 * X) * Real.sqrt (2 * Y)) *
              (((X / Real.exp 1) ^ (X - 1) * (Y / Real.exp 1) ^ (Y - 1)) *
                (α ^ (-α) * b ^ (-b)) ^ k) ≤
            (2 * (k : ℝ)) *
              (C₀ * ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 2)) :=
        mul_le_mul hsqrt hentropy
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (Real.rpow_nonneg (by positivity) _))
            (pow_nonneg (mul_nonneg (Real.rpow_nonneg hα.le _) (Real.rpow_nonneg hb.le _)) _))
          (mul_nonneg (by norm_num) (Nat.cast_nonneg k))
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hNq
      calc
        (Real.exp 4 * ((Real.sqrt (2 * X) * Real.sqrt (2 * Y)) *
            ((X / Real.exp 1) ^ (X - 1) * (Y / Real.exp 1) ^ (Y - 1))) / D) *
              (α ^ (-α) * b ^ (-b)) ^ k =
          Real.exp 4 * ((Real.sqrt (2 * X) * Real.sqrt (2 * Y)) *
            (((X / Real.exp 1) ^ (X - 1) * (Y / Real.exp 1) ^ (Y - 1)) *
              (α ^ (-α) * b ^ (-b)) ^ k)) / D := by ring
        _ ≤ Real.exp 4 * ((2 * (k : ℝ)) *
            (C₀ * ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 2))) / D :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hboth (Real.exp_pos _).le)
            hDpos.le
        _ = _ := by ring
    _ = ((N / q) * Real.exp 4 * 2 * C₀) *
        (((k : ℝ) * ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 2)) / D) := by ring
    _ ≤ ((N / q) * Real.exp 4 * 2 * C₀) *
        (Real.exp 2 * (k : ℝ) ^ (-(3 / 2 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [D, Real.rpow_natCast] using hratio) (by positivity)
    _ = ((N / q) * Real.exp 4 * 2 * C₀ * Real.exp 2) *
        (k : ℝ) ^ (-(3 / 2 : ℝ)) := by ring

private theorem ch3E14_summable_norm_of_lt (p q N n : ℝ) (a : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p < q) (hN : 0 ≤ N) (hn : |n| ≤ N)
    (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) :
    Summable (fun k : ℕ => ‖(ch3E14Coeff p q n k : ℂ) * a ^ k‖) := by
  let α : ℝ := p / q
  let b : ℝ := (q - p) / q
  let B : ℝ := N / q
  let C : ℝ := (N / q) * Real.exp 4 * 2 *
    (Real.exp (4 * (N / q)) * (p / q) ^ (-(N / q) - 1) *
      ((q - p) / q) ^ (-(N / q) - 1)) * Real.exp 2
  have hα : 0 < α := by simp only [α]; positivity
  have hb : 0 < b := by simp only [b]; positivity
  have hB : 0 ≤ B := by simp only [B]; positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (max ((B + 3) / α) ((B + 3) / b))
  have hlarge : ∀ k : ℕ, K ≤ k → B + 3 ≤ α * k ∧ B + 3 ≤ b * k := by
    intro k hk
    have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hαK : (B + 3) / α < K := lt_of_le_of_lt (le_max_left _ _) hK
    have hbK : (B + 3) / b < K := lt_of_le_of_lt (le_max_right _ _) hK
    constructor
    · simpa [mul_comm] using (div_le_iff₀ hα).mp (hαK.le.trans hKk)
    · simpa [mul_comm] using (div_le_iff₀ hb).mp (hbK.le.trans hKk)
  have hbase : Summable (fun k : ℕ => (k : ℝ) ^ (-(3 / 2 : ℝ))) := by
    have h := (Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).2 (by norm_num)
    apply h.congr
    intro k
    exact (Real.rpow_neg (Nat.cast_nonneg k) (3 / 2 : ℝ)).symm
  have hmajor : Summable (fun k : ℕ => C * (k : ℝ) ^ (-(3 / 2 : ℝ))) :=
    hbase.mul_left C
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_atTop.2 ⟨K, fun k hk => hk⟩] with k hk
  have hklarge := hlarge k hk
  have hcoeff := ch3E14_coeff_radius_le_of_lt p q N n k hp hq hpq hN hn
    (by simpa only [B, α] using hklarge.1) (by simpa only [B, b] using hklarge.2)
  have hapow : ‖a‖ ^ k ≤ (p ^ (-p / q) * |p - q| ^ ((p - q) / q)) ^ k :=
    pow_le_pow_left₀ (norm_nonneg a) ha k
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
    norm_pow]
  calc
    |ch3E14Coeff p q n k| * ‖a‖ ^ k ≤
        |ch3E14Coeff p q n k| *
          (p ^ (-p / q) * |p - q| ^ ((p - q) / q)) ^ k :=
      mul_le_mul_of_nonneg_left hapow (abs_nonneg _)
    _ ≤ C * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by simpa only [C] using hcoeff

private theorem ch3E14_Gamma_add_nat (x : ℝ) (n : ℕ) (hx : 0 < x) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ j ∈ Finset.range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show x + (n + 1 : ℕ) = (x + n) + 1 by push_cast; ring,
        Real.Gamma_add_one (by positivity), ih, Finset.prod_range_succ]
      ring

private theorem ch3E14_shifted_factorial_le_prod (x : ℝ) (n : ℕ)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    (Nat.factorial n : ℝ) * ((n : ℝ) + 1) ^ x ≤
      ∏ j ∈ Finset.range n, (x + ((j + 1 : ℕ) : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hgm : ((n : ℝ) + 1) ^ (1 - x) * ((n : ℝ) + 2) ^ x ≤
          x + ((n : ℝ) + 1) := by
        have h := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hx₁) hx₀
          (by positivity : 0 ≤ (n : ℝ) + 1) (by positivity : 0 ≤ (n : ℝ) + 2)
          (by ring : (1 - x) + x = 1)
        nlinarith
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Finset.prod_range_succ]
      have hmul := mul_le_mul ih hgm (by positivity) (by positivity)
      have hpow : ((n : ℝ) + 1) ^ x * ((n : ℝ) + 1) ^ (1 - x) =
          (n : ℝ) + 1 := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        have hexp : x + (1 - x) = 1 := by ring
        rw [hexp, Real.rpow_one]
      have hbase : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
      calc
        ((n : ℝ) + 1) * (Nat.factorial n : ℝ) * ((n : ℝ) + 1 + 1) ^ x =
            (Nat.factorial n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ x := by
          rw [hbase]
          ring
        _ = (Nat.factorial n : ℝ) *
            (((n : ℝ) + 1) ^ x * ((n : ℝ) + 1) ^ (1 - x)) *
              ((n : ℝ) + 2) ^ x := by rw [hpow]
        _ =
            ((Nat.factorial n : ℝ) * ((n : ℝ) + 1) ^ x) *
              (((n : ℝ) + 1) ^ (1 - x) * ((n : ℝ) + 2) ^ x) := by
          ring
        _ ≤ (∏ j ∈ Finset.range n, (x + ((j + 1 : ℕ) : ℝ))) *
            (x + ((n : ℝ) + 1)) := hmul
        _ = _ := by push_cast; ring

private theorem ch3E14_exists_Gamma_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ℝ, 4 ≤ y →
      c * (Real.sqrt (2 * Real.pi * y) * (y / Real.exp 1) ^ (y - 1)) ≤
        Real.Gamma y := by
  obtain ⟨z, hz, hzmin⟩ := Real.exists_isMinOn_Gamma_Ioi
  let c₀ : ℝ := Real.Gamma z
  let c : ℝ := c₀ * Real.exp (-4) / 2
  have hc₀ : 0 < c₀ := by
    simp only [c₀]
    exact Real.Gamma_pos_of_pos (zero_lt_one.trans hz.1)
  have hc : 0 < c := by simp only [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro y hy
  let n : ℕ := ⌊y⌋₊
  let θ : ℝ := y - n
  let m : ℕ := n - 1
  have hy0 : 0 ≤ y := by linarith
  have hny : (n : ℝ) ≤ y := by simpa only [n] using Nat.floor_le hy0
  have hyn : y < (n : ℝ) + 1 := by simpa only [n] using Nat.lt_floor_add_one y
  have hn4 : 4 ≤ n := by
    have : (4 : ℝ) < (n : ℝ) + 1 := hy.trans_lt hyn
    have hn3 : (3 : ℝ) < n := by linarith
    exact_mod_cast hn3
  have hm3 : 3 ≤ m := by simp only [m]; omega
  have hθ₀ : 0 ≤ θ := by simp only [θ]; linarith
  have hθ₁ : θ ≤ 1 := by simp only [θ]; linarith
  have harg : θ + 1 + m = y := by
    simp only [θ]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  have hrec := ch3E14_Gamma_add_nat (θ + 1) m (by linarith)
  rw [harg] at hrec
  have hmin : c₀ ≤ Real.Gamma (θ + 1) := by
    exact hzmin (by simp only [Set.mem_Ioi]; linarith)
  have hprod := ch3E14_shifted_factorial_le_prod θ m hθ₀ hθ₁
  have hprodeq :
      (∏ j ∈ Finset.range m, (θ + ((j + 1 : ℕ) : ℝ))) =
        ∏ j ∈ Finset.range m, (θ + 1 + (j : ℝ)) := by
    apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  have hm1 : 1 ≤ m := by omega
  have hfact := Stirling.le_factorial_stirling m
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
  have hmpow : ((m : ℝ) / Real.exp 1) ^ θ ≤ (m : ℝ) ^ θ := by
    apply Real.rpow_le_rpow (by positivity) (by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith [Real.add_one_le_exp 1]) hθ₀
  have hexponent : (m : ℝ) + θ = y - 1 := by
    simp only [θ]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  have hpowers :
      (((m : ℝ) / Real.exp 1) ^ m) * (m : ℝ) ^ θ ≥
        ((m : ℝ) / Real.exp 1) ^ (y - 1) := by
    calc
      ((m : ℝ) / Real.exp 1) ^ (y - 1) =
          ((m : ℝ) / Real.exp 1) ^ ((m : ℝ) + θ) := by rw [hexponent]
      _ = (((m : ℝ) / Real.exp 1) ^ m) *
          ((m : ℝ) / Real.exp 1) ^ θ := by
        rw [Real.rpow_add (by positivity), Real.rpow_natCast]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmpow (pow_nonneg (by positivity) _)
  have hnmpow : ((m : ℝ) + 1) ^ θ ≥ (m : ℝ) ^ θ :=
    Real.rpow_le_rpow hmpos.le (by linarith) hθ₀
  have hraw : c₀ *
      (Real.sqrt (2 * Real.pi * m) *
        (((m : ℝ) / Real.exp 1) ^ (y - 1))) ≤ Real.Gamma y := by
    rw [hrec]
    calc
      c₀ * (Real.sqrt (2 * Real.pi * m) *
          ((m : ℝ) / Real.exp 1) ^ (y - 1)) ≤
        c₀ * (Real.sqrt (2 * Real.pi * m) *
          ((((m : ℝ) / Real.exp 1) ^ m) * (m : ℝ) ^ θ)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hpowers (Real.sqrt_nonneg _)) hc₀.le
      _ ≤ c₀ * ((Nat.factorial m : ℝ) * (m : ℝ) ^ θ) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_right hfact (Real.rpow_nonneg hmpos.le θ))) hc₀.le
      _ ≤ c₀ * ((Nat.factorial m : ℝ) * ((m : ℝ) + 1) ^ θ) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnmpow (Nat.cast_nonneg _)) hc₀.le
      _ ≤ Real.Gamma (θ + 1) *
          (∏ j ∈ Finset.range m, (θ + ((j + 1 : ℕ) : ℝ))) :=
        mul_le_mul hmin hprod (by positivity) (Real.Gamma_pos_of_pos (by linarith)).le
      _ = Real.Gamma (θ + 1) *
          (∏ j ∈ Finset.range m, (θ + 1 + (j : ℝ))) := by rw [hprodeq]
  have hmy : y - 2 ≤ (m : ℝ) := by
    simp only [m]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    linarith
  have hshifted : c₀ *
      (Real.sqrt (2 * Real.pi * (y - 2)) *
        (((y - 2) / Real.exp 1) ^ (y - 1))) ≤ Real.Gamma y := by
    have hsqrtm : Real.sqrt (2 * Real.pi * (y - 2)) ≤
        Real.sqrt (2 * Real.pi * m) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left hmy (mul_nonneg (by norm_num) Real.pi_pos.le)
    have hpowm : ((y - 2) / Real.exp 1) ^ (y - 1) ≤
        ((m : ℝ) / Real.exp 1) ^ (y - 1) := by
      apply Real.rpow_le_rpow (div_nonneg (by linarith) (Real.exp_pos 1).le)
        (div_le_div_of_nonneg_right hmy (Real.exp_pos 1).le) (by linarith)
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul hsqrtm hpowm
        (Real.rpow_nonneg (div_nonneg (by linarith) (Real.exp_pos 1).le) _)
        (Real.sqrt_nonneg _)) hc₀.le).trans hraw
  have hratio := ch3E14_shift_ratio_le y (y - 2) 2 (by linarith) (by norm_num)
    (by linarith) (by linarith) (by linarith)
  have hpowercompare : Real.exp (-4) * (y / Real.exp 1) ^ (y - 1) ≤
      ((y - 2) / Real.exp 1) ^ (y - 1) := by
    have hsplit : (y / Real.exp 1) ^ (y - 1) =
        (y / (y - 2)) ^ (y - 1) * ((y - 2) / Real.exp 1) ^ (y - 1) := by
      rw [← Real.mul_rpow (div_nonneg (by linarith) (by linarith))
        (div_nonneg (by linarith) (Real.exp_pos 1).le)]
      congr 1
      field_simp [show y - 2 ≠ 0 by linarith]
    rw [hsplit]
    have hexpinv : Real.exp (-4) * Real.exp 4 = 1 := by rw [← Real.exp_add]; norm_num
    have hratio' : (y / (y - 2)) ^ (y - 1) ≤ Real.exp 4 := by
      norm_num at hratio ⊢
      exact hratio
    have hshiftpow0 : 0 ≤ ((y - 2) / Real.exp 1) ^ (y - 1) :=
      Real.rpow_nonneg (div_nonneg (by linarith) (Real.exp_pos 1).le) _
    calc
      Real.exp (-4) *
          ((y / (y - 2)) ^ (y - 1) * ((y - 2) / Real.exp 1) ^ (y - 1)) ≤
        Real.exp (-4) *
          (Real.exp 4 * ((y - 2) / Real.exp 1) ^ (y - 1)) := by gcongr
      _ = _ := by rw [← mul_assoc, hexpinv, one_mul]
  have hsqrtcompare : Real.sqrt (2 * Real.pi * y) / 2 ≤
      Real.sqrt (2 * Real.pi * (y - 2)) := by
    have hrad : 2 * Real.pi * y ≤ 4 * (2 * Real.pi * (y - 2)) := by
      nlinarith [Real.pi_pos]
    have hs := Real.sqrt_le_sqrt hrad
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hs
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hs4] at hs
    linarith
  simp only [c]
  calc
    c₀ * Real.exp (-4) / 2 *
        (Real.sqrt (2 * Real.pi * y) * (y / Real.exp 1) ^ (y - 1)) =
      c₀ * ((Real.sqrt (2 * Real.pi * y) / 2) *
        (Real.exp (-4) * (y / Real.exp 1) ^ (y - 1))) := by ring
    _ ≤ c₀ * (Real.sqrt (2 * Real.pi * (y - 2)) *
        ((y - 2) / Real.exp 1) ^ (y - 1)) := by gcongr
    _ ≤ Real.Gamma y := hshifted

private theorem ch3E14_inverse_shift_ratio_le (u v B : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hB : 0 ≤ B) (huv : u ≤ v + B) (hBv : B ≤ v) (hu_one : 1 ≤ u)
    (hv_one : 1 ≤ v) :
    (u / v) ^ (v - 1) ≤ Real.exp (2 * B) := by
  by_cases huv_order : u ≤ v
  · have hratio : u / v ≤ 1 := (div_le_one hv).mpr huv_order
    exact (Real.rpow_le_one (div_nonneg hu.le hv.le) hratio (sub_nonneg.mpr hv_one)).trans
      (Real.one_le_exp (mul_nonneg (by norm_num) hB))
  · have hratio_one : 1 ≤ u / v := (one_le_div hv).mpr (le_of_not_ge huv_order)
    calc
      (u / v) ^ (v - 1) ≤ (u / v) ^ (u - 1) :=
        Real.rpow_le_rpow_of_exponent_le hratio_one (by linarith)
      _ ≤ Real.exp (2 * B) :=
        ch3E14_shift_ratio_le u v B hv hB huv hBv hu_one

private theorem ch3E14_radius_mul_q_of_gt (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : q < p) :
    (p ^ (-p / q) * |p - q| ^ ((p - q) / q)) * q =
      ((p - q) / q) ^ ((p - q) / q) * (p / q) ^ (-(p / q)) := by
  let α : ℝ := p / q
  let d : ℝ := (p - q) / q
  have hα : 0 < α := by simp only [α]; positivity
  have hd : 0 < d := by simp only [d]; positivity
  have hαd : α = d + 1 := by simp only [α, d]; field_simp; ring
  have hpbase : p = q * α := by simp only [α]; field_simp
  have hdbase : p - q = q * d := by simp only [d]; field_simp
  have hnegp : -p / q = -α := by simp only [α]; ring
  have hdiff : (p - q) / q = d := rfl
  have habs : |p - q| = p - q := abs_of_pos (sub_pos.mpr hpq)
  rw [hnegp, hdiff]
  change (p ^ (-α) * |p - q| ^ d) * q = d ^ d * α ^ (-α)
  rw [habs, hdbase, hpbase, Real.mul_rpow hq.le hd.le, Real.mul_rpow hq.le hα.le]
  have hzero : (1 : ℝ) + d + -α = 0 := by linarith
  calc
    (q ^ (-α) * α ^ (-α) * (q ^ d * d ^ d)) * q =
        (q ^ (1 : ℝ) * q ^ d * q ^ (-α)) * (d ^ d * α ^ (-α)) := by
          rw [Real.rpow_one]
          ring
    _ = q ^ ((1 : ℝ) + d + -α) * (d ^ d * α ^ (-α)) := by
      rw [Real.rpow_add hq, Real.rpow_add hq]
    _ = _ := by rw [hzero, Real.rpow_zero, one_mul]

private theorem ch3E14_prod_eq_Gamma_div (x : ℝ) (k : ℕ) (hk : 1 ≤ k) (hx : 0 < x) :
    (∏ j ∈ Finset.range (k - 1), (x - ((j + 1 : ℕ) : ℝ))) =
      Real.Gamma x / Real.Gamma (x - k + 1) := by
  have hrec := ch3E14_inv_Gamma_sub_nat x (k - 1)
  have harg : x - ((k - 1 : ℕ) : ℝ) = x - k + 1 := by
    rw [Nat.cast_sub hk]
    push_cast
    ring
  rw [harg] at hrec
  have hGamma : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have hprod :
      (∏ j ∈ Finset.range (k - 1), (x - ((j + 1 : ℕ) : ℝ))) =
        Real.Gamma x * (Real.Gamma (x - k + 1))⁻¹ := by
    apply (mul_right_cancel₀ hGamma)
    rw [hrec]
    field_simp
  simpa only [div_eq_mul_inv] using hprod

private theorem ch3E14_shifted_entropy_div_le (α d β B : ℝ) (k : ℕ)
    (hα : 0 < α) (hd : 0 < d) (hαd : α = d + 1) (hB : 0 ≤ B)
    (hβ : |β| ≤ B) (hkα : B + 1 ≤ α * k) (hkd : 2 * B + 2 ≤ d * k) :
    (((α * k + β) / Real.exp 1) ^ (α * k + β - 1) /
        (((d * k + β + 1) / Real.exp 1) ^ (d * k + β))) *
          (d ^ d * α ^ (-α)) ^ k ≤
      (Real.exp (4 * B + 2) * α ^ (B - 1) * (d ^ B + d ^ (-B))) *
        ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 1) := by
  let K : ℝ := k
  let X : ℝ := α * K + β
  let Z : ℝ := d * K + β + 1
  have hβbounds : -B ≤ β ∧ β ≤ B := abs_le.mp hβ
  have hK : 0 < K := by
    have hmul : 0 < α * K := by simp only [K] at hkα ⊢; nlinarith
    exact pos_of_mul_pos_right hmul hα.le
  have hαK : 0 < α * K := mul_pos hα hK
  have hdK : 0 < d * K := mul_pos hd hK
  have hX1 : 1 ≤ X := by simp only [X]; nlinarith
  have hZ1 : 1 ≤ Z := by simp only [Z]; nlinarith
  have hXupper : X ≤ α * K + B := by simp only [X]; linarith
  have hBKα : B ≤ α * K := by simp only [K] at hkα ⊢; linarith
  have hB1Z : B + 1 ≤ Z := by simp only [Z, K] at hkd ⊢; linarith
  have hdKupper : d * K ≤ Z + (B + 1) := by simp only [Z]; linarith
  have hratioX := ch3E14_shift_ratio_le X (α * K) B hαK hB hXupper hBKα hX1
  have hratioZ := ch3E14_inverse_shift_ratio_le (d * K) Z (B + 1) hdK
    (zero_lt_one.trans_le hZ1) (by linarith) hdKupper hB1Z (by linarith) hZ1
  have hratios :
      (X / (α * K)) ^ (X - 1) * (d * K / Z) ^ (Z - 1) ≤
        Real.exp (4 * B + 2) := by
    calc
      (X / (α * K)) ^ (X - 1) * (d * K / Z) ^ (Z - 1) ≤
          Real.exp (2 * B) * Real.exp (2 * (B + 1)) :=
        mul_le_mul hratioX hratioZ (by positivity) (Real.exp_pos _).le
      _ = Real.exp (4 * B + 2) := by rw [← Real.exp_add]; congr 1; ring
  have hα1 : 1 ≤ α := by linarith
  have hshiftα : α ^ (β - 1) ≤ α ^ (B - 1) :=
    Real.rpow_le_rpow_of_exponent_le hα1 (by linarith)
  have hshiftd : d ^ (-β) ≤ d ^ B + d ^ (-B) := by
    by_cases hd1 : 1 ≤ d
    · exact (Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hd.le _))
    · have hdle : d ≤ 1 := le_of_not_ge hd1
      exact (Real.rpow_le_rpow_of_exponent_ge hd hdle (by linarith)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hd.le _))
  have hshifts : α ^ (β - 1) * d ^ (-β) ≤
      α ^ (B - 1) * (d ^ B + d ^ (-B)) :=
    mul_le_mul hshiftα hshiftd (Real.rpow_nonneg hd.le _)
      (Real.rpow_nonneg hα.le _)
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hKE : 0 < K / Real.exp 1 := div_pos hK (Real.exp_pos 1)
  have hXsplit :
      (X / Real.exp 1) ^ (X - 1) =
        α ^ (X - 1) * (K / Real.exp 1) ^ (X - 1) *
          (X / (α * K)) ^ (X - 1) := by
    have hbase : X / Real.exp 1 = (α * (K / Real.exp 1)) * (X / (α * K)) := by
      field_simp
    rw [hbase, Real.mul_rpow (mul_nonneg hα.le hKE.le)
      (div_nonneg hXpos.le hαK.le), Real.mul_rpow hα.le hKE.le]
  have hZsplit :
      (Z / Real.exp 1) ^ (Z - 1) =
        d ^ (Z - 1) * (K / Real.exp 1) ^ (Z - 1) *
          (Z / (d * K)) ^ (Z - 1) := by
    have hbase : Z / Real.exp 1 = (d * (K / Real.exp 1)) * (Z / (d * K)) := by
      field_simp
    rw [hbase, Real.mul_rpow (mul_nonneg hd.le hKE.le)
      (div_nonneg hZpos.le hdK.le), Real.mul_rpow hd.le hKE.le]
  have hcritical : (d ^ d * α ^ (-α)) ^ k =
      d ^ (d * K) * α ^ (-α * K) := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hd.le, ← Real.rpow_mul hα.le]
  have hinvratio : ((Z / (d * K)) ^ (Z - 1))⁻¹ =
      (d * K / Z) ^ (Z - 1) := by
    rw [← Real.inv_rpow (div_nonneg hZpos.le hdK.le)]
    congr 1
    field_simp
  have hαcombine : α ^ (X - 1) * α ^ (-α * K) = α ^ (β - 1) := by
    rw [← Real.rpow_add hα]
    simp only [X]
    ring_nf
  have hdcombine : d ^ (d * K) / d ^ (Z - 1) = d ^ (-β) := by
    rw [← Real.rpow_sub hd]
    congr 1
    simp only [Z]
    ring
  have hKcombine : (K / Real.exp 1) ^ (X - 1) /
      (K / Real.exp 1) ^ (Z - 1) = (K / Real.exp 1) ^ (K - 1) := by
    rw [← Real.rpow_sub hKE]
    congr 1
    simp only [X, Z, hαd]
    ring
  have hZexp : d * (k : ℝ) + β = Z - 1 := by simp only [Z, K]; ring
  rw [show α * (k : ℝ) + β = X by rfl,
    show d * (k : ℝ) + β + 1 = Z by rfl, hZexp, hXsplit, hZsplit, hcritical]
  have hidentity :
      ((α ^ (X - 1) * (K / Real.exp 1) ^ (X - 1) * (X / (α * K)) ^ (X - 1)) /
          (d ^ (Z - 1) * (K / Real.exp 1) ^ (Z - 1) * (Z / (d * K)) ^ (Z - 1))) *
            (d ^ (d * K) * α ^ (-α * K)) =
        ((X / (α * K)) ^ (X - 1) * (d * K / Z) ^ (Z - 1)) *
          (α ^ (β - 1) * d ^ (-β)) * (K / Real.exp 1) ^ (K - 1) := by
    rw [← hαcombine, ← hdcombine, ← hKcombine, ← hinvratio]
    field_simp
  rw [hidentity]
  have hpair :
      ((X / (α * K)) ^ (X - 1) * (d * K / Z) ^ (Z - 1)) *
          (α ^ (β - 1) * d ^ (-β)) ≤
        Real.exp (4 * B + 2) * (α ^ (B - 1) * (d ^ B + d ^ (-B))) :=
    mul_le_mul hratios hshifts (by positivity) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (by nlinarith [hpair]) (Real.rpow_nonneg hKE.le _)

private theorem ch3E14_sqrt_ratio_gt (α d X Z : ℝ) (k : ℕ)
    (hα : 0 < α) (hd : 0 < d) (hZ : 0 < Z)
    (hXle : X ≤ 2 * α * k) (hdle : d * k ≤ 2 * Z) (hk : 1 ≤ k) :
    Real.sqrt (2 * X) /
        (Real.sqrt (2 * Real.pi * Z) * Real.sqrt (2 * Real.pi * k)) ≤
      (2 * Real.sqrt α / Real.sqrt d) * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let K : ℝ := k
  have hK : 0 < K := by simp only [K]; exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hnum : Real.sqrt (2 * X) ≤ 2 * Real.sqrt α * Real.sqrt K := by
    have hs := Real.sqrt_le_sqrt (show 2 * X ≤ 4 * (α * K) by
      simp only [K] at hXle ⊢
      nlinarith)
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have heq : Real.sqrt (4 * (α * K)) = 2 * Real.sqrt α * Real.sqrt K := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul hα.le, hs4]
      ring
    rw [heq] at hs
    exact hs
  have hdenZ : Real.sqrt d * Real.sqrt K ≤ Real.sqrt (2 * Real.pi * Z) := by
    rw [← Real.sqrt_mul hd.le]
    apply Real.sqrt_le_sqrt
    have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
    simp only [K] at hdle ⊢
    have hpiZ := mul_le_mul_of_nonneg_right hpi (show 0 ≤ 2 * Z by positivity)
    nlinarith
  have hdenK : Real.sqrt K ≤ Real.sqrt (2 * Real.pi * K) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.two_le_pi]
  have hden : Real.sqrt d * K ≤
      Real.sqrt (2 * Real.pi * Z) * Real.sqrt (2 * Real.pi * K) := by
    have hmul := mul_le_mul hdenZ hdenK (Real.sqrt_nonneg _) (by positivity)
    rw [mul_assoc, Real.mul_self_sqrt hK.le] at hmul
    exact hmul
  change Real.sqrt (2 * X) /
      (Real.sqrt (2 * Real.pi * Z) * Real.sqrt (2 * Real.pi * K)) ≤
    (2 * Real.sqrt α / Real.sqrt d) * K ^ (-(1 / 2 : ℝ))
  calc
    Real.sqrt (2 * X) /
        (Real.sqrt (2 * Real.pi * Z) * Real.sqrt (2 * Real.pi * K)) ≤
      (2 * Real.sqrt α * Real.sqrt K) / (Real.sqrt d * K) :=
        div_le_div₀ (by positivity) hnum (mul_pos (Real.sqrt_pos.2 hd) hK) hden
    _ = (2 * Real.sqrt α / Real.sqrt d) * K ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hK.le, ← Real.sqrt_eq_rpow]
      field_simp
      rw [Real.sq_sqrt hK.le]

private theorem ch3E14_power_ratio_gt (k : ℕ) (hk : 1 ≤ k) :
    (((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 1)) /
        (((k : ℝ) / Real.exp 1) ^ (k : ℝ)) = Real.exp 1 / k := by
  let K : ℝ := k
  let t : ℝ := K / Real.exp 1
  have hK : 0 < K := by simp only [K]; exact_mod_cast (Nat.zero_lt_of_lt hk)
  have ht : 0 < t := div_pos hK (Real.exp_pos 1)
  change t ^ (K - 1) / t ^ K = Real.exp 1 / K
  rw [← Real.rpow_sub ht]
  have hexp : K - 1 - K = (-1 : ℝ) := by ring
  rw [hexp, Real.rpow_neg_one]
  simp only [t]
  field_simp

private theorem ch3E14_inv_sqrt_mul_inv (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / k) =
      Real.exp 1 * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
  let K : ℝ := k
  have hK : 0 < K := by simp only [K]; exact_mod_cast (Nat.zero_lt_of_lt hk)
  change K ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / K) =
    Real.exp 1 * K ^ (-(3 / 2 : ℝ))
  rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + -1 by norm_num,
    Real.rpow_add hK, Real.rpow_neg_one]
  ring

set_option maxHeartbeats 800000 in
-- This estimate combines the upper and lower real-Gamma bounds.
private theorem ch3E14_coeff_radius_le_of_gt (p q N n c : ℝ) (k : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hpq : q < p) (hN : 0 ≤ N) (hn : |n| ≤ N)
    (hc : 0 < c)
    (hGamma : ∀ y : ℝ, 4 ≤ y →
      c * (Real.sqrt (2 * Real.pi * y) * (y / Real.exp 1) ^ (y - 1)) ≤ Real.Gamma y)
    (hkα : N / q + 4 ≤ (p / q) * k)
    (hkd : 2 * (N / q) + 4 ≤ ((p - q) / q) * k) :
    |ch3E14Coeff p q n k| *
        (p ^ (-p / q) * |p - q| ^ ((p - q) / q)) ^ k ≤
      ((N / q) * c⁻¹ * Real.exp 2 *
          (Real.exp (4 * (N / q) + 2) * (p / q) ^ (N / q - 1) *
            (((p - q) / q) ^ (N / q) + ((p - q) / q) ^ (-(N / q)))) *
          (2 * Real.sqrt (p / q) / Real.sqrt ((p - q) / q)) * Real.exp 1) *
        (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
  let α : ℝ := p / q
  let d : ℝ := (p - q) / q
  let B : ℝ := N / q
  let β : ℝ := n / q
  let X : ℝ := α * k + β
  let Z : ℝ := d * k + β + 1
  let R : ℝ := p ^ (-p / q) * |p - q| ^ ((p - q) / q)
  let C₀ : ℝ := Real.exp (4 * B + 2) * α ^ (B - 1) * (d ^ B + d ^ (-B))
  let U : ℝ := Real.exp 2 * (Real.sqrt (2 * X) * (X / Real.exp 1) ^ (X - 1))
  let V : ℝ := Real.sqrt (2 * Real.pi * Z) * (Z / Real.exp 1) ^ (Z - 1)
  let D : ℝ := Real.sqrt (2 * Real.pi * k) *
    ((k : ℝ) / Real.exp 1) ^ (k : ℝ)
  have hα : 0 < α := by simp only [α]; positivity
  have hd : 0 < d := by simp only [d]; positivity
  have hαd : α = d + 1 := by simp only [α, d]; field_simp; ring
  have hB : 0 ≤ B := by simp only [B]; positivity
  have hβ : |β| ≤ B := by
    simp only [β, B, abs_div, abs_of_pos hq]
    exact div_le_div_of_nonneg_right hn hq.le
  have hkα' : B + 4 ≤ α * k := by simpa only [B, α] using hkα
  have hkd' : 2 * B + 4 ≤ d * k := by simpa only [B, d] using hkd
  have hβbounds : -B ≤ β ∧ β ≤ B := abs_le.mp hβ
  have hX4 : 4 ≤ X := by simp only [X]; linarith
  have hZ4 : 4 ≤ Z := by simp only [Z]; linarith
  have hXpos : 0 < X := by linarith
  have hZpos : 0 < Z := by linarith
  have hk : 1 ≤ k := by
    have : (0 : ℝ) < k := by
      have : 0 < α * (k : ℝ) := by linarith
      exact pos_of_mul_pos_right this hα.le
    exact_mod_cast this
  have hxeq : (n + (k : ℝ) * p) / q = X := by
    simp only [X, α, β]
    field_simp
    ring
  have hprodscale := ch3E14_product_scale p q n k hq.ne'
  rw [hxeq] at hprodscale
  let P : ℝ := ∏ j ∈ Finset.range (k - 1), (X - ((j + 1 : ℕ) : ℝ))
  have hprodscale' :
      (∏ j ∈ Finset.range (k - 1),
        (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)) = q ^ (k - 1) * P := by
    simpa only [P] using hprodscale
  have hqpow : q ^ k = q ^ (k - 1) * q := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  have hradius : R * q = d ^ d * α ^ (-α) := by
    simpa only [R, α, d] using ch3E14_radius_mul_q_of_gt p q hp hq hpq
  have hRqpow : R ^ k * q ^ k = (d ^ d * α ^ (-α)) ^ k := by
    rw [← mul_pow, hradius]
  have hRq : q ^ (k - 1) * R ^ k * q = (d ^ d * α ^ (-α)) ^ k := by
    calc
      q ^ (k - 1) * R ^ k * q = R ^ k * (q ^ (k - 1) * q) := by ring
      _ = R ^ k * q ^ k := by rw [← hqpow]
      _ = _ := hRqpow
  have hcoeff :
      |ch3E14Coeff p q n k| * R ^ k =
        (|n| / q) * (|P| / (Nat.factorial k : ℝ)) * (d ^ d * α ^ (-α)) ^ k := by
    have hfactabs : |(Nat.factorial k : ℝ)| = (Nat.factorial k : ℝ) :=
      abs_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos k))
    rw [ch3E14Coeff, lagrangeSeriesCoefficient_of_ne_zero p q n (Nat.ne_of_gt hk),
      hprodscale']
    simp only [abs_div, abs_mul, hfactabs, abs_pow, abs_of_pos hq]
    field_simp
    calc
      |n| * q ^ (k - 1) * |P| * R ^ k * q =
          |n| * |P| * (q ^ (k - 1) * R ^ k * q) := by ring
      _ = |n| * |P| * (d ^ d * α ^ (-α)) ^ k := by rw [hRq]
  have hZarg : X - k + 1 = Z := by simp only [X, Z, hαd]; ring
  have hP := ch3E14_prod_eq_Gamma_div X k hk hXpos
  rw [hZarg] at hP
  have hPpos : 0 < P := by
    rw [show P = Real.Gamma X / Real.Gamma Z by simpa only [P] using hP]
    positivity
  have hGX := ch3E14_Gamma_le X (by linarith)
  have hGZ := hGamma Z hZ4
  have hPV : |P| ≤ U / (c * V) := by
    rw [abs_of_pos hPpos, show P = Real.Gamma X / Real.Gamma Z by simpa only [P] using hP]
    exact div_le_div₀ (by simp only [U]; positivity)
      (by simpa only [U] using hGX) (mul_pos hc (by simp only [V]; positivity))
      (by simpa only [V] using hGZ)
  have hDpos : 0 < D := by simp only [D]; positivity
  have hfactorial : D ≤ (Nat.factorial k : ℝ) := by
    simpa only [D, Real.rpow_natCast] using Stirling.le_factorial_stirling k
  have hentropy :
      (((X / Real.exp 1) ^ (X - 1)) / ((Z / Real.exp 1) ^ (Z - 1))) *
          (d ^ d * α ^ (-α)) ^ k ≤
        C₀ * ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 1) := by
    have h := ch3E14_shifted_entropy_div_le α d β B k hα hd hαd hB hβ
      (by linarith) (by linarith)
    simp only [X, Z, C₀]
    rw [show d * (k : ℝ) + β + 1 - 1 = d * (k : ℝ) + β by ring]
    exact h
  have hXle : X ≤ 2 * α * k := by simp only [X]; nlinarith
  have hdle : d * k ≤ 2 * Z := by simp only [Z]; nlinarith
  have hsqrt := ch3E14_sqrt_ratio_gt α d X Z k hα hd hZpos hXle hdle hk
  have hpower := ch3E14_power_ratio_gt k hk
  have hinvsqrt := ch3E14_inv_sqrt_mul_inv k hk
  have hNq : 0 ≤ N / q := div_nonneg hN hq.le
  have hC₀ : 0 ≤ C₀ := by simp only [C₀]; positivity
  have hcore :
      (U / (c * V) / D) * (d ^ d * α ^ (-α)) ^ k ≤
        (c⁻¹ * Real.exp 2) *
          (2 * Real.sqrt α / Real.sqrt d) * C₀ * Real.exp 1 *
            (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hrearrange :
        (U / (c * V) / D) * (d ^ d * α ^ (-α)) ^ k =
          (c⁻¹ * Real.exp 2) *
            (Real.sqrt (2 * X) /
              (Real.sqrt (2 * Real.pi * Z) * Real.sqrt (2 * Real.pi * k))) *
            ((((X / Real.exp 1) ^ (X - 1) / (Z / Real.exp 1) ^ (Z - 1)) *
              (d ^ d * α ^ (-α)) ^ k) /
                (((k : ℝ) / Real.exp 1) ^ (k : ℝ))) := by
      simp only [U, V, D]
      field_simp
    rw [hrearrange]
    have hentdiv :
        ((((X / Real.exp 1) ^ (X - 1) / (Z / Real.exp 1) ^ (Z - 1)) *
            (d ^ d * α ^ (-α)) ^ k) /
              (((k : ℝ) / Real.exp 1) ^ (k : ℝ))) ≤
          C₀ * (Real.exp 1 / k) := by
      calc
        (((X / Real.exp 1) ^ (X - 1) / (Z / Real.exp 1) ^ (Z - 1)) *
            (d ^ d * α ^ (-α)) ^ k) /
              (((k : ℝ) / Real.exp 1) ^ (k : ℝ)) ≤
          (C₀ * ((k : ℝ) / Real.exp 1) ^ ((k : ℝ) - 1)) /
              (((k : ℝ) / Real.exp 1) ^ (k : ℝ)) :=
            div_le_div_of_nonneg_right hentropy (Real.rpow_nonneg (by positivity) _)
        _ = C₀ * (Real.exp 1 / k) := by rw [mul_div_assoc, hpower]
    calc
      (c⁻¹ * Real.exp 2) *
          (Real.sqrt (2 * X) /
            (Real.sqrt (2 * Real.pi * Z) * Real.sqrt (2 * Real.pi * k))) *
          ((((X / Real.exp 1) ^ (X - 1) / (Z / Real.exp 1) ^ (Z - 1)) *
            (d ^ d * α ^ (-α)) ^ k) /
              (((k : ℝ) / Real.exp 1) ^ (k : ℝ))) ≤
        (c⁻¹ * Real.exp 2) *
          ((2 * Real.sqrt α / Real.sqrt d) * (k : ℝ) ^ (-(1 / 2 : ℝ))) *
            (C₀ * (Real.exp 1 / k)) := by gcongr
      _ = (c⁻¹ * Real.exp 2) * (2 * Real.sqrt α / Real.sqrt d) * C₀ *
          ((k : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.exp 1 / k)) := by ring
      _ = _ := by rw [hinvsqrt]; ring
  rw [show p ^ (-p / q) * |p - q| ^ ((p - q) / q) = R by rfl,
    show p / q = α by rfl, show (p - q) / q = d by rfl,
    show N / q = B by rfl]
  rw [hcoeff]
  calc
    (|n| / q) * (|P| / (Nat.factorial k : ℝ)) * (d ^ d * α ^ (-α)) ^ k ≤
      (N / q) * ((U / (c * V)) / D) * (d ^ d * α ^ (-α)) ^ k := by
        gcongr
    _ ≤ (N / q) * ((c⁻¹ * Real.exp 2) *
          (2 * Real.sqrt α / Real.sqrt d) * C₀ * Real.exp 1 *
            (k : ℝ) ^ (-(3 / 2 : ℝ))) :=
      by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hcore hNq
    _ = ((N / q) * c⁻¹ * Real.exp 2 * C₀ *
          (2 * Real.sqrt α / Real.sqrt d) * Real.exp 1) *
        (k : ℝ) ^ (-(3 / 2 : ℝ)) := by ring

private theorem ch3E14_summable_norm_of_gt (p q N n : ℝ) (a : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : q < p) (hN : 0 ≤ N) (hn : |n| ≤ N)
    (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) :
    Summable (fun k : ℕ => ‖(ch3E14Coeff p q n k : ℂ) * a ^ k‖) := by
  obtain ⟨c, hc, hGamma⟩ := ch3E14_exists_Gamma_lower
  let α : ℝ := p / q
  let d : ℝ := (p - q) / q
  let B : ℝ := N / q
  let C : ℝ := (N / q) * c⁻¹ * Real.exp 2 *
    (Real.exp (4 * (N / q) + 2) * (p / q) ^ (N / q - 1) *
      (((p - q) / q) ^ (N / q) + ((p - q) / q) ^ (-(N / q)))) *
    (2 * Real.sqrt (p / q) / Real.sqrt ((p - q) / q)) * Real.exp 1
  have hα : 0 < α := by simp only [α]; positivity
  have hd : 0 < d := by simp only [d]; positivity
  have hB : 0 ≤ B := by simp only [B]; positivity
  obtain ⟨K, hK⟩ := exists_nat_gt
    (max ((B + 4) / α) ((2 * B + 4) / d))
  have hlarge : ∀ k : ℕ, K ≤ k →
      B + 4 ≤ α * k ∧ 2 * B + 4 ≤ d * k := by
    intro k hk
    have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hαK : (B + 4) / α < K := lt_of_le_of_lt (le_max_left _ _) hK
    have hdK : (2 * B + 4) / d < K := lt_of_le_of_lt (le_max_right _ _) hK
    constructor
    · simpa [mul_comm] using (div_le_iff₀ hα).mp (hαK.le.trans hKk)
    · simpa [mul_comm] using (div_le_iff₀ hd).mp (hdK.le.trans hKk)
  have hbase : Summable (fun k : ℕ => (k : ℝ) ^ (-(3 / 2 : ℝ))) := by
    have h := (Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).2 (by norm_num)
    apply h.congr
    intro k
    exact (Real.rpow_neg (Nat.cast_nonneg k) (3 / 2 : ℝ)).symm
  have hmajor : Summable (fun k : ℕ => C * (k : ℝ) ^ (-(3 / 2 : ℝ))) :=
    hbase.mul_left C
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_atTop.2 ⟨K, fun k hk => hk⟩] with k hk
  have hklarge := hlarge k hk
  have hcoeff := ch3E14_coeff_radius_le_of_gt p q N n c k hp hq hpq hN hn hc hGamma
    (by simpa only [B, α] using hklarge.1) (by simpa only [B, d] using hklarge.2)
  have hapow : ‖a‖ ^ k ≤ (p ^ (-p / q) * |p - q| ^ ((p - q) / q)) ^ k :=
    pow_le_pow_left₀ (norm_nonneg a) ha k
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
    norm_pow]
  calc
    |ch3E14Coeff p q n k| * ‖a‖ ^ k ≤
        |ch3E14Coeff p q n k| *
          (p ^ (-p / q) * |p - q| ^ ((p - q) / q)) ^ k :=
      mul_le_mul_of_nonneg_left hapow (abs_nonneg _)
    _ ≤ C * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by simpa only [C] using hcoeff

private theorem ch3E14_summable_norm (p q N n : ℝ) (a : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) (hN : 0 ≤ N) (hn : |n| ≤ N)
    (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) :
    Summable (fun k : ℕ => ‖(ch3E14Coeff p q n k : ℂ) * a ^ k‖) := by
  rcases lt_or_gt_of_ne hpq with hpq | hpq
  · exact ch3E14_summable_norm_of_lt p q N n a hp hq hpq hN hn ha
  · exact ch3E14_summable_norm_of_gt p q N n a hp hq hpq hN hn ha

private theorem ch3E14_coeff_crude (p q N n : ℝ) (k : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 ≤ N) (hn : |n| ≤ N) :
    |ch3E14Coeff p q n k| ≤
      (1 + N) * (1 + N + (k : ℝ) * (p + q)) ^ k := by
  by_cases hk : k = 0
  · subst k
    simp [ch3E14Coeff]
    linarith
  · let M : ℝ := 1 + N + (k : ℝ) * (p + q)
    have hM : 1 ≤ M := by
      simp only [M]
      nlinarith [mul_nonneg (Nat.cast_nonneg k) (add_nonneg hp.le hq.le)]
    have hfactor : ∀ j ∈ Finset.range (k - 1),
        |n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q| ≤ M := by
      intro j hj
      have hjk : j + 1 ≤ k := by
        have : j < k - 1 := Finset.mem_range.mp hj
        omega
      have hjk' : ((j + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hjk
      calc
        |n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q| ≤
            |n + (k : ℝ) * p| + |((j + 1 : ℕ) : ℝ) * q| := abs_sub _ _
        _ ≤ |n| + |(k : ℝ) * p| + |((j + 1 : ℕ) : ℝ) * q| := by
          gcongr
          exact abs_add_le _ _
        _ = |n| + (k : ℝ) * p + ((j + 1 : ℕ) : ℝ) * q := by
          rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hp.le),
            abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hq.le)]
        _ ≤ M := by simp only [M]; nlinarith
    have hprod :
        |∏ j ∈ Finset.range (k - 1),
            (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)| ≤ M ^ (k - 1) := by
      rw [Finset.abs_prod]
      calc
        (∏ j ∈ Finset.range (k - 1),
            |n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q|) ≤
          ∏ _j ∈ Finset.range (k - 1), M := by
            exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hfactor
        _ = M ^ (k - 1) := by rw [Finset.prod_const, Finset.card_range]
    have hfact : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by
      exact_mod_cast (show 1 ≤ Nat.factorial k by have := Nat.factorial_pos k; omega)
    have hfactabs : |(Nat.factorial k : ℝ)| = (Nat.factorial k : ℝ) :=
      abs_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos k))
    rw [ch3E14Coeff, lagrangeSeriesCoefficient_of_ne_zero p q n hk]
    simp only [abs_div, abs_mul, hfactabs]
    calc
      |n| * |∏ j ∈ Finset.range (k - 1),
          (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)| /
            (Nat.factorial k : ℝ) ≤ |n| * M ^ (k - 1) := by
              calc
                |n| * |∏ j ∈ Finset.range (k - 1),
                    (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)| /
                      (Nat.factorial k : ℝ) ≤
                  |n| * |∏ j ∈ Finset.range (k - 1),
                    (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q)| :=
                      div_le_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hfact
                _ ≤ |n| * M ^ (k - 1) :=
                  mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ ≤ (1 + N) * M ^ k := by
        exact mul_le_mul (by linarith) (pow_le_pow_right₀ hM (Nat.sub_le k 1))
          (pow_nonneg (zero_le_one.trans hM) _) (by linarith)
      _ = _ := rfl

private theorem ch3E14_exists_uniform_majorant (p q N : ℝ) (a : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) (hN : 0 ≤ N)
    (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℝ, |n| ≤ N → ∀ k : ℕ,
      ‖(ch3E14Coeff p q n k : ℂ) * a ^ k‖ ≤ u k := by
  let R : ℝ := p ^ (-p / q) * |p - q| ^ ((p - q) / q)
  have hR : 0 ≤ R := by simp only [R]; positivity
  have assemble (C : ℝ) (K : ℕ) (hC : 0 ≤ C)
      (hbound : ∀ n : ℝ, |n| ≤ N → ∀ k : ℕ, K ≤ k →
        |ch3E14Coeff p q n k| * R ^ k ≤ C * (k : ℝ) ^ (-(3 / 2 : ℝ))) :
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℝ, |n| ≤ N → ∀ k : ℕ,
        ‖(ch3E14Coeff p q n k : ℂ) * a ^ k‖ ≤ u k := by
    let e : ℕ → ℝ := fun k => if k < K then
      (1 + N) * (1 + N + (k : ℝ) * (p + q)) ^ k * R ^ k else 0
    let u : ℕ → ℝ := fun k => e k + C * (k : ℝ) ^ (-(3 / 2 : ℝ))
    have he : Summable e := by
      apply summable_of_ne_finset_zero (s := Finset.range K)
      intro k hk
      have hnot : ¬k < K := fun h => hk (Finset.mem_range.mpr h)
      simp [e, hnot]
    have hbase : Summable (fun k : ℕ => (k : ℝ) ^ (-(3 / 2 : ℝ))) := by
      have h := (Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).2 (by norm_num)
      apply h.congr
      intro k
      exact (Real.rpow_neg (Nat.cast_nonneg k) (3 / 2 : ℝ)).symm
    have hu : Summable u := by
      simpa only [u] using he.add (hbase.mul_left C)
    refine ⟨u, hu, ?_⟩
    intro n hn k
    have hapow : ‖a‖ ^ k ≤ R ^ k := pow_le_pow_left₀ (norm_nonneg a) (by simpa only [R] using ha) k
    have hterm : ‖(ch3E14Coeff p q n k : ℂ) * a ^ k‖ ≤
        |ch3E14Coeff p q n k| * R ^ k := by
      rw [norm_mul, Complex.norm_real, norm_pow]
      exact mul_le_mul_of_nonneg_left hapow (abs_nonneg _)
    by_cases hk : k < K
    · have hcrude := ch3E14_coeff_crude p q N n k hp hq hN hn
      apply hterm.trans
      simp only [u, e, hk, ↓reduceIte]
      have hearly : |ch3E14Coeff p q n k| * R ^ k ≤
          (1 + N) * (1 + N + (k : ℝ) * (p + q)) ^ k * R ^ k :=
        mul_le_mul_of_nonneg_right hcrude (pow_nonneg hR k)
      exact hearly.trans (le_add_of_nonneg_right
        (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg k) _)))
    · apply hterm.trans
      simp only [u, e, hk, ↓reduceIte]
      simpa only [zero_add] using hbound n hn k (le_of_not_gt hk)
  rcases lt_or_gt_of_ne hpq with hpq | hpq
  · let α : ℝ := p / q
    let b : ℝ := (q - p) / q
    let B : ℝ := N / q
    let C : ℝ := (N / q) * Real.exp 4 * 2 *
      (Real.exp (4 * (N / q)) * (p / q) ^ (-(N / q) - 1) *
        ((q - p) / q) ^ (-(N / q) - 1)) * Real.exp 2
    have hα : 0 < α := by simp only [α]; positivity
    have hb : 0 < b := by simp only [b]; positivity
    have hB : 0 ≤ B := by simp only [B]; positivity
    obtain ⟨K, hK⟩ := exists_nat_gt (max ((B + 3) / α) ((B + 3) / b))
    apply assemble C K (by simp only [C]; positivity)
    intro n hn k hk
    have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hαk : B + 3 ≤ α * k := by
      simpa [mul_comm] using (div_le_iff₀ hα).mp
        ((lt_of_le_of_lt (le_max_left _ _) hK).le.trans hKk)
    have hbk : B + 3 ≤ b * k := by
      simpa [mul_comm] using (div_le_iff₀ hb).mp
        ((lt_of_le_of_lt (le_max_right _ _) hK).le.trans hKk)
    simpa only [R, C, B, α, b] using
      ch3E14_coeff_radius_le_of_lt p q N n k hp hq hpq hN hn hαk hbk
  · obtain ⟨c, hc, hGamma⟩ := ch3E14_exists_Gamma_lower
    let α : ℝ := p / q
    let d : ℝ := (p - q) / q
    let B : ℝ := N / q
    let C : ℝ := (N / q) * c⁻¹ * Real.exp 2 *
      (Real.exp (4 * (N / q) + 2) * (p / q) ^ (N / q - 1) *
        (((p - q) / q) ^ (N / q) + ((p - q) / q) ^ (-(N / q)))) *
      (2 * Real.sqrt (p / q) / Real.sqrt ((p - q) / q)) * Real.exp 1
    have hα : 0 < α := by simp only [α]; positivity
    have hd : 0 < d := by simp only [d]; positivity
    have hB : 0 ≤ B := by simp only [B]; positivity
    obtain ⟨K, hK⟩ := exists_nat_gt
      (max ((B + 4) / α) ((2 * B + 4) / d))
    apply assemble C K (by simp only [C]; positivity)
    intro n hn k hk
    have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hαk : B + 4 ≤ α * k := by
      simpa [mul_comm] using (div_le_iff₀ hα).mp
        ((lt_of_le_of_lt (le_max_left _ _) hK).le.trans hKk)
    have hdk : 2 * B + 4 ≤ d * k := by
      simpa [mul_comm] using (div_le_iff₀ hd).mp
        ((lt_of_le_of_lt (le_max_right _ _) hK).le.trans hKk)
    simpa only [R, C, B, α, d] using
      ch3E14_coeff_radius_le_of_gt p q N n c k hp hq hpq hN hn hc hGamma hαk hdk

private noncomputable def ch3E14Term (p q : ℝ) (a : ℂ) (n : ℝ) (k : ℕ) : ℂ :=
  (ch3E14Coeff p q n k : ℂ) * a ^ k

private noncomputable def ch3E14F (p q : ℝ) (a : ℂ) (n : ℝ) : ℂ :=
  ∑' k : ℕ, ch3E14Term p q a n k

private theorem ch3E14Term_continuous (p q : ℝ) (a : ℂ) (k : ℕ) :
    Continuous (fun n : ℝ => ch3E14Term p q a n k) := by
  have hcoeff : Continuous (fun n : ℝ => ch3E14Coeff p q n k) := by
    convert (ch3E14Polynomial p q k).continuous using 1
    ext n
    exact (ch3E14Polynomial_eval p q n k).symm
  exact (Complex.continuous_ofReal.comp hcoeff).mul continuous_const

private theorem ch3E14Term_hasSum (p q : ℝ) (a : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) (n : ℝ) :
    HasSum (ch3E14Term p q a n) (ch3E14F p q a n) := by
  apply Summable.hasSum
  exact (ch3E14_summable_norm p q |n| n a hp hq hpq (abs_nonneg n) le_rfl ha).of_norm

private theorem ch3E14F_continuous (p q : ℝ) (a : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) :
    Continuous (ch3E14F p q a) := by
  rw [continuous_iff_continuousAt]
  intro x
  let N : ℝ := |x| + 1
  have hN : 0 ≤ N := by simp only [N]; positivity
  obtain ⟨u, hu, hmajor⟩ :=
    ch3E14_exists_uniform_majorant p q N a hp hq hpq hN ha
  have hcont : ContinuousOn (ch3E14F p q a) (Set.Icc (-N) N) := by
    exact continuousOn_tsum (fun k => (ch3E14Term_continuous p q a k).continuousOn) hu
      (fun k n hn => hmajor n (abs_le.mpr hn) k)
  apply hcont.continuousAt
  apply Icc_mem_nhds
  · simp only [N]
    nlinarith [neg_abs_le x]
  · simp only [N]
    nlinarith [le_abs_self x]

@[simp]
private theorem ch3E14F_zero (p q : ℝ) (a : ℂ) : ch3E14F p q a 0 = 1 := by
  simp only [ch3E14F]
  calc
    (∑' k : ℕ, ch3E14Term p q a 0 k) =
        ∑' k : ℕ, if k = 0 then (1 : ℂ) else 0 := by
          apply tsum_congr
          intro k
          by_cases hk : k = 0 <;> simp [ch3E14Term, ch3E14Coeff_zero_param, hk]
    _ = 1 := tsum_ite_eq 0 1

private theorem ch3E14F_add (p q : ℝ) (a : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) (r s : ℝ) :
    ch3E14F p q a r * ch3E14F p q a s = ch3E14F p q a (r + s) := by
  have hr : Summable (fun k : ℕ => ‖ch3E14Term p q a r k‖) := by
    simpa only [ch3E14Term] using
      ch3E14_summable_norm p q |r| r a hp hq hpq (abs_nonneg r) le_rfl ha
  have hs : Summable (fun k : ℕ => ‖ch3E14Term p q a s k‖) := by
    simpa only [ch3E14Term] using
      ch3E14_summable_norm p q |s| s a hp hq hpq (abs_nonneg s) le_rfl ha
  rw [ch3E14F, ch3E14F, ch3E14F,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hr hs]
  apply tsum_congr
  intro m
  calc
    (∑ k ∈ Finset.range (m + 1),
        ch3E14Term p q a r k * ch3E14Term p q a s (m - k)) =
        ((∑ k ∈ Finset.range (m + 1),
          ch3E14Coeff p q r k * ch3E14Coeff p q s (m - k) : ℝ) : ℂ) * a ^ m := by
            rw [Complex.ofReal_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            simp only [ch3E14Term]
            rw [Complex.ofReal_mul]
            have hpow : a ^ k * a ^ (m - k) = a ^ m := by
              rw [← pow_add, Nat.add_sub_of_le hkm]
            rw [← hpow]
            ring
    _ = ch3E14Term p q a (r + s) m := by
      rw [ch3E14Coeff_add p q r s m]
      rfl

private theorem ch3E14Coeff_shift (p q : ℝ) (m : ℕ) :
    ch3E14Coeff p q q (m + 1) = q * ch3E14Coeff p q p m := by
  have h := ch3E14Coeff_sub p q q m
  have harg : q + p - q = p := by ring
  rw [sub_self, harg, ch3E14Coeff_zero_param] at h
  simpa using h

private theorem ch3E14Term_shift (p q : ℝ) (a : ℂ) (m : ℕ) :
    ch3E14Term p q a q (m + 1) = a * (q : ℂ) * ch3E14Term p q a p m := by
  simp only [ch3E14Term, ch3E14Coeff_shift, Complex.ofReal_mul, pow_succ]
  ring

private theorem ch3E14F_shift (p q : ℝ) (a : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) :
    ch3E14F p q a q = 1 + a * (q : ℂ) * ch3E14F p q a p := by
  have hsumq := (ch3E14Term_hasSum p q a hp hq hpq ha q).summable
  calc
    ch3E14F p q a q = ch3E14Term p q a q 0 +
        ∑' m : ℕ, ch3E14Term p q a q (m + 1) := by
          rw [ch3E14F, hsumq.tsum_eq_zero_add]
    _ = 1 + ∑' m : ℕ, ch3E14Term p q a q (m + 1) := by
      simp [ch3E14Term]
    _ = 1 + ∑' m : ℕ, a * (q : ℂ) * ch3E14Term p q a p m := by
      congr 1
      exact tsum_congr (ch3E14Term_shift p q a)
    _ = 1 + a * (q : ℂ) * ch3E14F p q a p := by
      rw [tsum_mul_left]
      rfl

private theorem ch3E14Term_eq_frozen_summand (p q n : ℝ) (a : ℂ) (k : ℕ) :
    (if k = 0 then (1 : ℂ) else (n : ℂ) *
      Finset.prod (Finset.range (k - 1))
        (fun j => (n : ℂ) + (k : ℂ) * (p : ℂ) - ((j + 1 : ℂ) * (q : ℂ))) * a ^ k /
          (Nat.factorial k : ℂ)) = ch3E14Term p q a n k := by
  by_cases hk : k = 0
  · subst k
    simp [ch3E14Term]
  · simp only [hk, ↓reduceIte]
    rw [ch3E14Term, ch3E14Coeff,
      lagrangeSeriesCoefficient_of_ne_zero p q n hk]
    push_cast
    ring

/-- **Ramanujan's Lagrange series.** Let $p > 0$ and $q > 0$ be real numbers with $p \ne q$, and
let $a$ be a complex number with $|a| \le p^{-p/q} |p - q|^{(p - q)/q}$. Then there is a complex
number $L$ with $a q e^{p L} - e^{q L} + 1 = 0$ such that, for every real number $n$, the series
$$1 + \sum_{k=1}^{\infty} \frac{n a^k}{k!} \prod_{j=1}^{k-1} (n + k p - j q)$$
converges unconditionally to $e^{n L}$.

Proves `Wanted` entry `ramanujan_part1_ch3_entry14_lagrange_series`.

Proof: The argument uses the Hagen--Rothe convolution, a Stirling-type coefficient bound uniform
through the boundary circle, and a continuous exponential lift.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 14, formulas
    (14.1)--(14.5), printed pp. 70--71 / PDF pp. 80--81; attribution on printed p. 72 / PDF p.
    82.
-/
theorem ramanujan_part1_ch3_entry14_lagrange_series (p q : ℝ)
    (hp : 0 < p)
        (hq : 0 < q) (hpq : p ≠ q) (a : ℂ) (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) :
    ∃ L : ℂ, a * (↑q : ℂ) * Complex.exp (↑p * L) - Complex.exp (↑q * L) + 1 = 0 ∧ ∀ n : ℝ,
        HasSum (fun k : ℕ => if k = 0 then (1 : ℂ) else (↑n : ℂ) *
            Finset.prod (Finset.range (k - 1))
                (fun j => (↑n : ℂ) + (k : ℂ) * (↑p : ℂ) - ((j + 1 : ℂ) * (↑q : ℂ))) * a ^ k /
                    (↑(Nat.factorial k) : ℂ)) (Complex.exp ((↑n : ℂ) * L)) := by
  obtain ⟨L, hL⟩ := MetaMathlibExt.exists_eq_exp_mul_of_continuous_add_mul (ch3E14F p q a)
    (ch3E14F_continuous p q a hp hq hpq ha) (ch3E14F_zero p q a)
    (fun r s => (ch3E14F_add p q a hp hq hpq ha r s).symm)
  refine ⟨L, ?_, ?_⟩
  · have hshift := ch3E14F_shift p q a hp hq hpq ha
    rw [hL q, hL p] at hshift
    rw [hshift]
    ring
  · intro n
    have hsum := ch3E14Term_hasSum p q a hp hq hpq ha n
    rw [hL n] at hsum
    convert hsum using 1
    funext k
    exact ch3E14Term_eq_frozen_summand p q n a k

end Entry14LagrangeSeries

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3

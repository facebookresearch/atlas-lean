/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.RingTheory.PowerSeries.Exp
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution

/-!
# A binomial sum of Euler and Lucas numbers

The Euler secant series cancels the even exponential factor of the Lucas series.
Taking coefficients gives the binomial sum in Corollary 10 of Bensaci, Boumahdi and Khaldi,
*Finite Sums Involving Fibonacci and Lucas Numbers*, Journal of Integer Sequences 27 (2024),
Article 24.7.2.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

open MetaMathlibExt

/-- **Euler numbers.** For a natural number $n$, the Euler number $E_n \in \mathbb{Q}$ is $0$ when
$n$ is odd, and when $n = 2k$ is even it is the even-index Euler number $E_{2k}$, where
$E_0 = 1$ and $\sum_{i=0}^{k} \binom{2k}{2i} E_{2i} = 0$ for $k \ge 1$. The first values are
$E_0 = 1$, $E_2 = -1$, $E_4 = 5$.

These are the Euler (secant) numbers, with exponential generating function $2/(e^t + e^{-t})$. -/
noncomputable def eulerSecNumber (n : ℕ) : ℚ :=
  if n % 2 = 1 then 0
  else ((MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry.chapter5EulerEven
    (n / 2) : ℤ) : ℚ)

open Finset PowerSeries
open scoped goldenRatio
open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry

private theorem eulerSecNumber_two_mul (m : ℕ) :
    eulerSecNumber (2 * m) = (chapter5EulerEven m : ℚ) := by
  rw [eulerSecNumber, ite_eq_right (by omega), show (2 * m) / 2 = m by omega]

-- Only even indices contribute when all odd coefficients vanish.
private theorem sum_even_indices (g : ℕ → ℝ) (m : ℕ) (hg : ∀ k, Odd k → g k = 0) :
    ∑ k ∈ range (2 * m + 1), g k = ∑ j ∈ range (m + 1), g (2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
      sum_range_succ, sum_range_succ, hg (2 * m + 1) ⟨m, by omega⟩, add_zero, ih,
      show (2 * m + 1) + 1 = 2 * (m + 1) by omega,
      sum_range_succ (fun j : ℕ ↦ g (2 * j)) (m + 1)]

-- The coefficients of the product with the even exponential, before dividing by n!.
private theorem sum_choose_secant_even (n : ℕ) :
    ∑ k ∈ range (n + 1), (if (n - k) % 2 = 0 then
        (n.choose k : ℝ) * (eulerSecNumber k : ℝ) else 0) = if n = 0 then 1 else 0 := by
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, he⟩
    rw [sum_even_indices _ _ (fun k hk ↦ by simp [eulerSecNumber, Nat.odd_iff.mp hk])]
    simp_rw [show ∀ k : ℕ, (2 * m - 2 * k) % 2 = 0 by omega, ite_true,
      eulerSecNumber_two_mul, Rat.cast_intCast]
    rcases eq_or_ne m 0 with rfl | hm
    · simp [chapter5EulerEven_zero]
    · have h := chapter5EulerEven_recurrence m
      rw [ite_eq_right hm] at h
      rw [ite_eq_right (by omega : 2 * m ≠ 0)]
      simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero] using
        congrArg (Int.cast : ℤ → ℝ) h
  · rw [ite_eq_right (by omega : n ≠ 0)]
    refine sum_eq_zero fun k hk ↦ ?_
    have hk' : k ≤ n := mem_range_succ_iff.mp hk
    by_cases h : (n - k) % 2 = 0
    · have hodd : k % 2 = 1 := by omega
      simp [h, eulerSecNumber, hodd]
    · simp [h]

private noncomputable def secantSeries : PowerSeries ℝ :=
  mk fun n ↦ (eulerSecNumber n : ℝ) / n.factorial

private noncomputable abbrev expSeries (a : ℝ) : PowerSeries ℝ := rescale a (exp ℝ)

private theorem coeff_secantSeries (n : ℕ) :
    coeff n secantSeries = (eulerSecNumber n : ℝ) / n.factorial := coeff_mk n _

private theorem coeff_expSeries (a : ℝ) (n : ℕ) :
    coeff n (expSeries a) = a ^ n / n.factorial := by
  simp [expSeries, coeff_rescale, coeff_exp, div_eq_mul_inv, mul_comm]

private theorem coeff_exp_add_exp_neg (n : ℕ) :
    coeff n (expSeries 1 + expSeries (-1)) =
      if n % 2 = 0 then 2 / (n.factorial : ℝ) else 0 := by
  rw [map_add, coeff_expSeries, coeff_expSeries, one_pow, ← add_div]
  by_cases h : n % 2 = 0
  · rw [ite_eq_left h, (Nat.even_iff.mpr h).neg_one_pow]
    norm_num
  · rw [ite_eq_right h, (Nat.odd_iff.mpr (by omega : n % 2 = 1)).neg_one_pow]
    simp

private theorem secantSeries_mul_exp_add_exp_neg :
    secantSeries * (expSeries 1 + expSeries (-1)) = C (2 : ℝ) := by
  ext n
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_C]
  calc
    _ = (2 / (n.factorial : ℝ)) * ∑ k ∈ range (n + 1),
        (if (n - k) % 2 = 0 then (n.choose k : ℝ) * (eulerSecNumber k : ℝ) else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk ↦ ?_
      rw [coeff_secantSeries, coeff_exp_add_exp_neg]
      split_ifs
      · rw [Nat.cast_choose ℝ (mem_range_succ_iff.mp hk)]
        field_simp
      · simp
    _ = _ := by rw [sum_choose_secant_even]; split_ifs <;> simp_all

private theorem secantSeries_mul_lucasSeries :
    rescale (Real.sqrt 5 / 2) secantSeries * (expSeries φ + expSeries ψ) =
      C (2 : ℝ) * expSeries (1 / 2) := by
  let a : ℝ := Real.sqrt 5 / 2
  have hscale : rescale a secantSeries * (expSeries a + expSeries (-a)) = C (2 : ℝ) := by
    have h := congrArg (rescale a) secantSeries_mul_exp_add_exp_neg
    have hc : rescale a (C (2 : ℝ)) = C (2 : ℝ) := by
      ext n
      rw [coeff_rescale, coeff_C]
      split_ifs <;> simp_all
    simpa only [map_mul, map_add, expSeries, rescale_rescale, one_mul, neg_mul, hc] using h
  have hφ : a + 1 / 2 = φ := by dsimp [a, Real.goldenRatio]; ring
  have hψ : -a + 1 / 2 = ψ := by dsimp [a, Real.goldenConj]; ring
  change rescale a secantSeries * (expSeries φ + expSeries ψ) = C (2 : ℝ) * expSeries (1 / 2)
  unfold expSeries at hscale ⊢
  rw [← hφ, ← hψ, ← exp_mul_exp_eq_exp_add a (1 / 2), ← exp_mul_exp_eq_exp_add (-a) (1 / 2),
    ← add_mul, ← mul_assoc, hscale]

/-- **A binomial sum of Euler and Lucas numbers.** Let $L_n$ be the Lucas numbers and let $E_k$
be the Euler (secant) numbers, given by $2/(e^t + e^{-t}) = \sum_{k \ge 0} E_k t^k / k!$. For
every natural number $n$,
$$\sum_{k=0}^{n} \binom{n}{k} \left(\frac{\sqrt{5}}{2}\right)^{k} E_k L_{n-k} = \frac{2}{2^n}.$$

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 10. -/
theorem sum_choose_eulerSec_lucas (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * ((Real.sqrt 5) / 2) ^ k *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) =
      2 / 2 ^ n := by
  calc
    _ = (n.factorial : ℝ) * coeff n
        (rescale (Real.sqrt 5 / 2) secantSeries * (expSeries φ + expSeries ψ)) := by
      rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
      refine sum_congr rfl fun k hk ↦ ?_
      rw [coeff_rescale, coeff_secantSeries, map_add, coeff_expSeries, coeff_expSeries,
        ← add_div, cb_lucas_binet, Nat.cast_choose ℝ (mem_range_succ_iff.mp hk)]
      field_simp
    _ = _ := by
      rw [secantSeries_mul_lucasSeries, coeff_C_mul, coeff_expSeries, div_pow, one_pow]
      field_simp

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

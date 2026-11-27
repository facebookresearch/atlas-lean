/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.PowerFree
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Finite
import MathlibExt.NumberTheory.FactorialDivisor

/-!
# Brocard–Ramanujan solutions with a power-free neighbour

Statement from Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with
7-Free Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(i).

If `n! + 1 = x ^ 2`, then `x - 1` and `x + 1` both divide `n! = (x - 1) (x + 1)`. When one of
them is `k`-free, every exponent in its prime factorization is below `k`, so Lemma 1 of the
paper (`MetaMathlibExt.le_exp_of_dvd_factorial`) bounds it by `exp (3 n k / 2)`. Hence
`n! < x ^ 2 ≤ 4 exp (3 k) ^ n`, which fails for all large `n` because the factorial outgrows
every exponential. So `n` is bounded, and `x` with it.
-/

open Nat

namespace MetaMathlibExt

namespace BrocardRamanujanPowerFree

/-- A positive `k`-free natural number dividing `n!` is at most `exp (3 n k / 2)`. -/
private theorem le_exp_of_isPowerFree_dvd_factorial {n y k : ℕ} (hn : 0 < n)
    (hy : y.IsPowerFree k) (hdvd : y ∣ n !) :
    (y : ℝ) ≤ Real.exp (3 * n * k / 2) := by
  have hy0 : y ≠ 0 := hy.pos.ne'
  have hK : y.primeFactors.sup y.factorization < k := by
    rw [Finset.sup_lt_iff (by simp only [bot_eq_zero']; have := hy.two_le; omega)]
    intro p hp
    have hprime := prime_of_mem_primeFactors hp
    by_contra hle
    exact hy.not_dvd hprime ((hprime.pow_dvd_iff_le_factorization hy0).mpr (not_lt.mp hle))
  refine (le_exp_of_dvd_factorial hn hy.pos hdvd).trans (Real.exp_le_exp.mpr ?_)
  have hK' : ((y.primeFactors.sup y.factorization : ℕ) : ℝ) ≤ k := by
    exact_mod_cast hK.le
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  gcongr

/-- A solution of `n! + 1 = x ^ 2` with `x - 1` or `x + 1` being `k`-free and `n ≥ 1` satisfies
`n! < 4 ⌈exp (3 k)⌉₊ ^ n`. -/
private theorem factorial_lt {n x k : ℕ} (hn : 0 < n) (hsol : n ! + 1 = x ^ 2)
    (hfree : (x - 1).IsPowerFree k ∨ (x + 1).IsPowerFree k) :
    n ! < 4 * ⌈Real.exp (3 * k)⌉₊ ^ n := by
  have hx : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · simp at hsol
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
  have hfac : n ! = m * (m + 2) := by
    have : n ! + 1 = m * (m + 2) + 1 := by rw [hsol]; ring
    omega
  -- Some `y ∈ {m, m + 2}` is `k`-free, divides `n!` and satisfies `m + 1 ≤ 2 y`.
  obtain ⟨y, hyfree, hydvd, hxy⟩ : ∃ y : ℕ, y.IsPowerFree k ∧ y ∣ n ! ∧ m + 1 ≤ 2 * y := by
    rcases hfree with h | h
    · simp only [Nat.add_sub_cancel] at h
      exact ⟨m, h, hfac ▸ dvd_mul_right _ _, by have := h.pos; omega⟩
    · exact ⟨m + 2, h, hfac ▸ dvd_mul_left _ _, by omega⟩
  have hy := le_exp_of_isPowerFree_dvd_factorial hn hyfree hydvd
  have hxy' : ((m + 1 : ℕ) : ℝ) ≤ 2 * y := by exact_mod_cast hxy
  have hm0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : (((m + 1) ^ 2 : ℕ) : ℝ) ≤ 4 * Real.exp (3 * k) ^ n := by
    rw [← Real.exp_nat_mul]
    have h2 : Real.exp (3 * n * k / 2) ^ 2 = Real.exp (n * (3 * k)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc (((m + 1) ^ 2 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
      _ ≤ (2 * y) ^ 2 := by gcongr
      _ ≤ (2 * Real.exp (3 * n * k / 2)) ^ 2 := by gcongr
      _ = 4 * Real.exp (n * (3 * k)) := by rw [mul_pow, h2]; norm_num
  have hceil : Real.exp (3 * k) ^ n ≤ (⌈Real.exp (3 * k)⌉₊ : ℝ) ^ n := by
    gcongr
    exact Nat.le_ceil _
  have hlt : ((n ! : ℕ) : ℝ) < ((4 * ⌈Real.exp (3 * k)⌉₊ ^ n : ℕ) : ℝ) := by
    push_cast
    have : ((n ! : ℕ) : ℝ) + 1 = (((m + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hsol
    linarith
  exact_mod_cast hlt

end BrocardRamanujanPowerFree

-- `2 ≤ k` is already part of `IsPowerFree`, so the statement's `hk` is not needed.
set_option linter.unusedVariables false in
open BrocardRamanujanPowerFree in
/-- **Brocard–Ramanujan solutions with $x - 1$ or $x + 1$ power-free are finite.** For every
natural number $k \ge 2$, there are only finitely many pairs of natural numbers $(n, x)$ with
$n! + 1 = x^2$ such that $x - 1$ or $x + 1$ is $k$-free.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(i), first
sentence (`integers-2025-A71-thm-1`). -/
public theorem brocardRamanujan_powerFree_finite (k : ℕ) (hk : 2 ≤ k) :
    {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
      ((p.2 - 1).IsPowerFree k ∨ (p.2 + 1).IsPowerFree k)}.Finite := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Nat.eventually_mul_pow_lt_factorial_sub 4 ⌈Real.exp (3 * k)⌉₊ 0)
  refine ((Set.finite_Iio (N + 1)).prod (Set.finite_Iic ((N + 1)! + 1))).subset ?_
  rintro ⟨n, x⟩ ⟨hsol, hfree⟩
  dsimp only at hsol hfree
  have hnN : n < N + 1 := by
    by_contra hge
    have h1 := hN n (by omega)
    have h2 := factorial_lt (by omega) hsol hfree
    rw [Nat.sub_zero] at h1
    omega
  refine ⟨hnN, ?_⟩
  change x ≤ (N + 1)! + 1
  calc x ≤ x ^ 2 := Nat.le_self_pow (by norm_num) x
    _ = n ! + 1 := hsol.symm
    _ ≤ (N + 1)! + 1 := by gcongr

end MetaMathlibExt

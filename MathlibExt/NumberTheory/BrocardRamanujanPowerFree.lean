/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.PowerFree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.FactorialDivisor

/-!
# Brocard–Ramanujan solutions with a power-free or prime-power neighbour

Statements from Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with
7-Free Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(i) and (ii).

If `n! + 1 = x ^ 2`, then `x - 1` and `x + 1` both divide `n! = (x - 1) (x + 1)`. When one of
them is `k`-free, every exponent in its prime factorization is below `k`, so Lemma 1 of the
paper (`MetaMathlibExt.le_exp_of_dvd_factorial`) bounds it by `exp (3 n k / 2)`. Hence
`n! < x ^ 2 ≤ 4 exp (3 k) ^ n`, which fails for all large `n` because the factorial outgrows
every exponential. So `n` is bounded, and `x` with it.

## References

* Abderrahim Makki Naciri, *On the Brocard–Ramanujan Equation with 7-Free Integers and Prime
  Powers*, INTEGERS 25 (2025), Article A71, pp. 1–8, Lemma 1 and Theorem 1(i) and (ii).
-/

open Nat

namespace MetaMathlibExt

namespace BrocardRamanujanPowerFree

/-- A positive `k`-free natural number dividing `n!` is at most `exp (3 n k / 2)`. -/
public theorem le_exp_of_isPowerFree_dvd_factorial {n y k : ℕ} (hn : 0 < n)
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

private theorem four_pow_le_factorial {n : ℕ} (hn : 7 ≤ n) : 4 ^ (n - 1) ≤ n ! := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ, Nat.factorial_succ]
    calc
      _ ≤ n ! * 4 := Nat.mul_le_mul_right 4 ih
      _ ≤ n ! * (n + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := Nat.mul_comm _ _

private theorem le_two_pow_of_primePow_mul_eq_factorial {n a b : ℕ} (hn : n ≠ 0)
    (ha : IsPrimePow a) (ha₂ : 2 ∣ a) (hb₂ : 2 ∣ b) (hab : a * b = n !) :
    a ≤ 2 ^ (n - 2) := by
  obtain ⟨q, e, hq, -, rfl⟩ := (isPrimePow_nat_iff a).mp ha
  obtain rfl : 2 = q := Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hq ha₂
  -- Only evenness of the other factor is needed: it contributes at least one more two.
  have hdvd : 2 ^ (e + 1) ∣ n ! := by
    rw [pow_succ, ← hab]
    exact Nat.mul_dvd_mul (dvd_refl _) hb₂
  have he := (Nat.pow_dvd_iff_le_multiplicity Nat.prime_two.ne_one
    (Nat.factorial_ne_zero n)).mp hdvd
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hval := multiplicity_factorial_lt_of_ne_zero (p := 2) hn
  exact Nat.pow_le_pow_right (by decide) (by omega)

private theorem not_primePow_of_seven_le {n x : ℕ} (hn : 7 ≤ n) (hsol : n ! + 1 = x ^ 2)
    (hprime : IsPrimePow (x - 1) ∨ IsPrimePow (x + 1)) : False := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hsol
  obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
  have hfac : n ! = m * (m + 2) := by
    have : n ! + 1 = m * (m + 2) + 1 := by rw [hsol]; ring
    omega
  have hdiv : 2 ∣ n ! := Nat.dvd_factorial (by decide) (by omega)
  rw [hfac, Nat.prime_two.dvd_mul] at hdiv
  have hm₂ : 2 ∣ m := by omega
  have hm₂' : 2 ∣ m + 2 := by omega
  have hm : m ≤ 2 ^ (n - 2) := by
    rcases hprime with h | h
    · rw [Nat.add_sub_cancel] at h
      exact le_two_pow_of_primePow_mul_eq_factorial (by omega) h hm₂ hm₂' hfac.symm
    · have hfac' := (Nat.mul_comm (m + 2) m).trans hfac.symm
      have := le_two_pow_of_primePow_mul_eq_factorial (by omega) h hm₂' hm₂ hfac'
      omega
  have hxle : m + 1 ≤ 2 ^ (n - 1) := by
    have hpos : 0 < (2 : ℕ) ^ (n - 2) := pow_pos (by decide) _
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    omega
  have hle : (m + 1) ^ 2 ≤ n ! := calc
    _ ≤ (2 ^ (n - 1)) ^ 2 := Nat.pow_le_pow_left hxle 2
    _ = 4 ^ (n - 1) := by rw [pow_two, ← mul_pow, show (2 : ℕ) * 2 = 4 by decide]
    _ ≤ _ := four_pow_le_factorial hn
  omega

private theorem sq_ne_of_between {m x : ℕ} (a : ℕ) (hlo : a ^ 2 < m)
    (hhi : m < (a + 1) ^ 2) : x ^ 2 ≠ m := by
  intro h
  rcases le_or_gt x a with hxa | hax
  · exact (not_le_of_gt hlo) (h ▸ Nat.pow_le_pow_left hxa 2)
  · exact (not_le_of_gt hhi) (h ▸ Nat.pow_le_pow_left hax 2)

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

open BrocardRamanujanPowerFree in
/-- **Brocard–Ramanujan solutions with $x - 1$ or $x + 1$ a prime power.** If natural numbers
$n$ and $x$ satisfy $n! + 1 = x^2$ and $x - 1$ or $x + 1$ is a prime power, then
$(n, x) = (4, 5)$.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(ii),
second sentence (`integers-2025-A71-thm-1`). -/
public theorem brocardRamanujan_primePow_subset :
    {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧ (IsPrimePow (p.2 - 1) ∨ IsPrimePow (p.2 + 1))} ⊆
      {(4, 5)} := by
  rintro ⟨n, x⟩ ⟨hsol, hprime⟩
  dsimp only at hsol hprime
  by_cases hn : 7 ≤ n
  · exact (not_primePow_of_seven_le hn hsol hprime).elim
  · interval_cases n <;> norm_num [Nat.factorial] at hsol
    · exact (sq_ne_of_between 1 (by decide) (by decide) hsol.symm).elim
    · exact (sq_ne_of_between 1 (by decide) (by decide) hsol.symm).elim
    · exact (sq_ne_of_between 1 (by decide) (by decide) hsol.symm).elim
    · exact (sq_ne_of_between 2 (by decide) (by decide) hsol.symm).elim
    · have hx : x = 5 := Nat.pow_left_injective (by decide : 2 ≠ 0) hsol.symm
      subst x
      exact Set.mem_singleton _
    · have hx : x = 11 := Nat.pow_left_injective (by decide : 2 ≠ 0) hsol.symm
      subst x
      exact (show ¬ (IsPrimePow (11 - 1 : ℕ) ∨ IsPrimePow (11 + 1 : ℕ)) by decide) hprime |>.elim
    · exact (sq_ne_of_between 26 (by decide) (by decide) hsol.symm).elim

end MetaMathlibExt

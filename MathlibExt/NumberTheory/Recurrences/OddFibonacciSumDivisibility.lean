/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import MathlibExt.NumberTheory.Recurrences.FibonacciPrimeDivisibility
import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibility

/-!
# Odd divisors of their Fibonacci partial sums

Infinitely many odd natural numbers divide the sum of the first that many Fibonacci numbers.
The witnesses are Fibonacci numbers with index `2 * p` for primes `p ≡ 17 [MOD 30]`.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

namespace infinite_setOf_odd_dvd_sum_fib

private theorem fib_cast_periodic {m d : ℕ} (hd : pisanoPeriod m ∣ d) :
    Function.Periodic (fun n => (Nat.fib n : ZMod m)) d := by
  let step : ZMod m × ZMod m → ZMod m × ZMod m := fun p => (p.2, p.1 + p.2)
  have hstep : Function.IsPeriodicPt step d (0, 1) :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hd
  let castPair : ℕ × ℕ → ZMod m × ZMod m := fun p => (p.1, p.2)
  have hcast : Function.Semiconj castPair (fun p => (p.2, p.1 + p.2)) step := by
    intro p
    simp [castPair, step]
  have hiter (n : ℕ) : (Nat.fib n : ZMod m) = (step^[n] (0, 1)).1 := by
    simpa [Nat.fib, castPair] using congrArg Prod.fst (hcast.iterate_right n (0, 1))
  intro n
  change (Nat.fib (n + d) : ZMod m) = (Nat.fib n : ZMod m)
  rw [hiter, hiter]
  exact congrArg Prod.fst (hstep.periodic_iterate n)

private theorem fib_two_mul_cast_eq_neg_one {p : ℕ} (hp : p.Prime) (hp₂ : 2 < p)
    (hp₅ : p % 5 = 2) : (Nat.fib (2 * p) : ZMod p) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hleg : legendreSym p 5 ≠ 1 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p)
      (by decide) (by omega)
    simp only [Nat.cast_ofNat] at hrec
    rw [hrec, legendreSym.mod, ← Int.natCast_mod, hp₅]
    exact (by decide : @legendreSym 5 ⟨Nat.prime_five⟩ 2 ≠ 1)
  have hzero : (Nat.fib (p + 1) : ZMod p) = 0 := by
    apply (CharP.cast_eq_zero_iff (ZMod p) p _).mpr
    simpa [hleg] using MetaMathlibExt.fib_prime_dvd_fib_of_legendre_sub p (by omega) hp₂
  -- Cassini gives the square of F_p modulo p, which suffices for the doubling identity.
  have hc := Int.fib_succ_mul_fib_pred_sub_fib_sq (p : ℤ)
  rw [Int.natAbs_natCast, (hp.odd_of_ne_two (by omega)).neg_one_pow, ← Nat.cast_add_one] at hc
  rw [Int.fib_natCast (p + 1), Int.fib_natCast p] at hc
  have hcmod := congrArg (Int.cast : ℤ → ZMod p) hc
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast, hzero,
    zero_mul, zero_sub, Int.cast_neg, Int.cast_one] at hcmod
  have hle : Nat.fib p ≤ 2 * Nat.fib (p + 1) := Nat.fib_le_fib_succ.trans (by omega)
  rw [Nat.fib_two_mul, Nat.cast_mul, Nat.cast_sub hle, Nat.cast_mul, hzero,
    mul_zero, zero_sub, mul_neg, ← pow_two]
  exact hcmod

private theorem fib_two_mul_odd_and_dvd_sum {p : ℕ} (hp : p.Prime) (hp₃₀ : p % 30 = 17) :
    Odd (Nat.fib (2 * p)) ∧ Nat.fib (2 * p) ∣
      (∑ i ∈ Finset.Icc 1 (Nat.fib (2 * p)), Nat.fib i) := by
  let k := Nat.fib (2 * p)
  have hmod₄ : k % 4 = 3 := by
    apply (ZMod.natCast_eq_natCast_iff' k 3 4).mp
    have hperiod : pisanoPeriod 4 ∣ 6 := by
      rw [pisanoPeriod, ← Function.isPeriodicPt_iff_minimalPeriod_dvd]
      decide
    change (Nat.fib (2 * p) : ZMod 4) = (3 : ℕ)
    rw [← (fib_cast_periodic hperiod).map_mod_nat (2 * p), show (2 * p) % 6 = 4 by omega]
    rfl
  refine ⟨Nat.odd_iff.mpr (by omega), ?_⟩
  have hpDvd : p ∣ k + 1 := by
    apply (CharP.cast_eq_zero_iff (ZMod p) p _).mp
    change ((Nat.fib (2 * p) + 1 : ℕ) : ZMod p) = 0
    rw [Nat.cast_add, Nat.cast_one, fib_two_mul_cast_eq_neg_one hp (by omega) (by omega),
      neg_add_cancel]
  have hcoprime : Nat.Coprime 4 p :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬ 2 ∣ p)).pow_left 2
  have hdiv : 4 * p ∣ k + 1 := hcoprime.mul_dvd_of_dvd_of_dvd (by omega) hpDvd
  have hperiod : pisanoPeriod k ∣ 4 * p := by
    rw [show 4 * p = 2 * (2 * p) by omega]
    exact pisanoPeriod_fib_dvd_two_mul (2 * p) (by omega) (dvd_mul_right 2 p)
  have hfib : (Nat.fib (k + 2) : ZMod k) = 1 := by
    simpa [show 1 + (k + 1) = k + 2 by omega] using fib_cast_periodic (hperiod.trans hdiv) 1
  have hIcc : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsum : (∑ i ∈ Finset.Icc 1 k, Nat.fib i) + 1 = Nat.fib (k + 2) := by
    rw [Nat.fib_succ_eq_succ_sum (k + 1), hIcc, Finset.sum_insert (by simp),
      Nat.fib_zero, zero_add]
  apply (CharP.cast_eq_zero_iff (ZMod k) k _).mp
  apply add_right_cancel (b := (1 : ZMod k))
  simpa [Nat.cast_add, hfib] using congrArg (Nat.cast : ℕ → ZMod k) hsum

end infinite_setOf_odd_dvd_sum_fib

open infinite_setOf_odd_dvd_sum_fib in
/-- **Infinitely many odd $k$ divide the sum of the first $k$ Fibonacci numbers.** Let $F_i$ denote
the $i$-th Fibonacci number, with $F_1 = F_2 = 1$. There are infinitely many odd positive integers
$k$ such that $k$ divides $F_1 + F_2 + \dots + F_k$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Corollary 2. -/
public theorem infinite_setOf_odd_dvd_sum_fib
    :
    {k : ℕ | Odd k ∧ k ∣ (∑ i ∈ Finset.Icc 1 k, Nat.fib i)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨p, hpn, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max n 5)
    (q := 30) (a := 17) (by decide) (by decide)
  have hp₃₀ : p % 30 = 17 := hmod
  refine ⟨Nat.fib (2 * p), fib_two_mul_odd_and_dvd_sum hp hp₃₀, ?_⟩
  exact (show n < 2 * p by omega).trans_le (Nat.le_fib_self (by omega))

end MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

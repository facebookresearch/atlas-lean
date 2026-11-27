/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import MathlibExt.NumberTheory.Recurrences.FibonacciPrimeDivisibility
import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibility

/-!
# Fibonacci sum divisibility at indices twice or four times a prime

Flynn-Connolly's Theorem 2 uses the periods modulo `4`, `8`, and `Nat.fib n`.
-/

namespace MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

-- The pair iteration follows `FibonacciSumDivisibility.lean`; the periodicity and Cassini
-- arguments are adapted from `OddFibonacciSumDivisibility.lean`.
private theorem iterate_fib_pair (m n : ℕ) :
    (fun a : ZMod m × ZMod m => (a.2, a.1 + a.2))^[n] (0, 1) =
      ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, Nat.fib_add_two, Nat.cast_add]

private theorem fib_cast_periodic {m d : ℕ} (hd : pisanoPeriod m ∣ d) :
    Function.Periodic (fun n => (Nat.fib n : ZMod m)) d := by
  have hstep : Function.IsPeriodicPt (fun a : ZMod m × ZMod m => (a.2, a.1 + a.2))
      d (0, 1) := Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hd
  intro n
  simpa only [iterate_fib_pair] using congrArg Prod.fst (hstep.periodic_iterate n)

private theorem fib_two_mul_cast (m a : ℕ) :
    (Nat.fib (2 * a) : ZMod m) = Nat.fib a * (2 * Nat.fib (a + 1) - Nat.fib a) := by
  have hle : Nat.fib a ≤ 2 * Nat.fib (a + 1) := Nat.fib_le_fib_succ.trans (by omega)
  rw [Nat.fib_two_mul, Nat.cast_mul, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]

private theorem fib_cast_prime_indices {p : ℕ} (hp : p.Prime) (hp₂ : 2 < p)
    (hp₅ : p % 5 = 2 ∨ p % 5 = 3) :
    (Nat.fib (2 * p) : ZMod p) = -1 ∧ (Nat.fib (4 * p) : ZMod p) = -3 := by
  let : Fact p.Prime := ⟨hp⟩
  have hleg : legendreSym p 5 ≠ 1 := by
    let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p)
      (by decide) (by omega)
    simp only [Nat.cast_ofNat] at hrec
    rw [hrec, legendreSym.mod, ← Int.natCast_mod]
    rcases hp₅ with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  have hzero : (Nat.fib (p + 1) : ZMod p) = 0 := by
    apply (CharP.cast_eq_zero_iff (ZMod p) p _).mpr
    simpa only [ite_eq_right hleg] using
      MetaMathlibExt.fib_prime_dvd_fib_of_legendre_sub p (by omega) hp₂
  have hc := Int.fib_succ_mul_fib_pred_sub_fib_sq (p : ℤ)
  rw [Int.natAbs_natCast, (hp.odd_of_ne_two (by omega)).neg_one_pow, ← Nat.cast_add_one] at hc
  rw [Int.fib_natCast (p + 1), Int.fib_natCast p] at hc
  have hcmod := congrArg (Int.cast : ℤ → ZMod p) hc
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast, hzero,
    zero_mul, zero_sub, Int.cast_neg, Int.cast_one] at hcmod
  have hsquare : (Nat.fib p : ZMod p) ^ 2 = 1 := neg_inj.mp hcmod
  have hdouble : (Nat.fib (2 * p) : ZMod p) = -1 := by
    rw [fib_two_mul_cast, hzero, mul_zero, zero_sub, mul_neg, ← pow_two, hsquare]
  have hnext : (Nat.fib (2 * p + 1) : ZMod p) = 1 := by
    rw [Nat.fib_two_mul_add_one, Nat.cast_add, Nat.cast_pow, Nat.cast_pow, hzero, zero_pow
      (by decide : (2 : ℕ) ≠ 0), zero_add, hsquare]
  refine ⟨hdouble, ?_⟩
  rw [show 4 * p = 2 * (2 * p) by omega, fib_two_mul_cast, hdouble, hnext]
  ring

/-- **Odd Fibonacci numbers $F_n$ with $F_{F_n + 2} \equiv 1 \pmod{F_n}$.** Let $F_m$ denote the
$m$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. If $p$ is an odd prime with
$p \equiv 2 \pmod 3$ and $p \equiv 2$ or $3 \pmod 5$, and $n = 2p$ or $n = 4p$, then $F_n$ is odd
and $F_{F_n + 2}$ leaves remainder $1$ on division by $F_n$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Theorem 2. -/
public theorem fib_two_mul_prime_odd_and_fib_fib_add_two_mod
    (p n : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1)
    (hp3 : p % 3 = 2) (hp5 : p % 5 = 2 ∨ p % 5 = 3)
    (hn : n = 2 * p ∨ n = 4 * p) :
    Nat.fib n % 2 = 1 ∧
      Nat.fib (Nat.fib n + 2) % Nat.fib n = 1 := by
  have hp₂ : 2 < p := by have := hp.two_le; omega
  have hn₃ : 3 ≤ n := by rcases hn with h | h <;> omega
  have hn₂ : 2 ∣ n := by
    rcases hn with rfl | rfl
    · exact dvd_mul_right 2 p
    · exact ⟨2 * p, by omega⟩
  let k := Nat.fib n
  have hk : 1 < k := calc
    1 < Nat.fib 3 := by decide
    _ ≤ k := Nat.fib_mono hn₃
  have hperiod : pisanoPeriod k ∣ 2 * n :=
    pisanoPeriod_fib_dvd_two_mul n (by omega) hn₂
  obtain ⟨hdouble, hquadruple⟩ := fib_cast_prime_indices hp hp₂ hp5
  have hcoprime : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have hresult : k % 2 = 1 ∧ (Nat.fib (k + 2) : ZMod k) = 1 := by
    rcases hn with rfl | rfl
    · have hmod : k % 4 = 3 := by
        apply (ZMod.natCast_eq_natCast_iff' k 3 4).mp
        have hper : pisanoPeriod 4 ∣ 6 := by
          rw [pisanoPeriod, ← Function.isPeriodicPt_iff_minimalPeriod_dvd]
          decide
        change (Nat.fib (2 * p) : ZMod 4) = (3 : ℕ)
        rw [← (fib_cast_periodic hper).map_mod_nat (2 * p), show (2 * p) % 6 = 4 by omega]
        rfl
      have hpDvd : p ∣ k + 1 := by
        apply (CharP.cast_eq_zero_iff (ZMod p) p _).mp
        change ((Nat.fib (2 * p) + 1 : ℕ) : ZMod p) = 0
        rw [Nat.cast_add, Nat.cast_one, hdouble, neg_add_cancel]
      have hdiv : 2 * (2 * p) ∣ k + 1 := by
        rw [show 2 * (2 * p) = 4 * p by omega]
        exact (hcoprime.pow_left 2).mul_dvd_of_dvd_of_dvd (by omega) hpDvd
      refine ⟨by omega, ?_⟩
      simpa only [show 1 + (k + 1) = k + 2 by omega, Nat.fib_one, Nat.cast_one] using
        fib_cast_periodic (hperiod.trans hdiv) 1
    · have hmod : k % 8 = 5 := by
        apply (ZMod.natCast_eq_natCast_iff' k 5 8).mp
        have hper : pisanoPeriod 8 ∣ 12 := by
          rw [pisanoPeriod, ← Function.isPeriodicPt_iff_minimalPeriod_dvd]
          decide
        change (Nat.fib (4 * p) : ZMod 8) = (5 : ℕ)
        rw [← (fib_cast_periodic hper).map_mod_nat (4 * p), show (4 * p) % 12 = 8 by omega]
        rfl
      have hpDvd : p ∣ k + 3 := by
        apply (CharP.cast_eq_zero_iff (ZMod p) p _).mp
        change ((Nat.fib (4 * p) + 3 : ℕ) : ZMod p) = 0
        rw [Nat.cast_add, Nat.cast_ofNat, hquadruple, neg_add_cancel]
      have hdiv : 2 * (4 * p) ∣ k + 3 := by
        rw [show 2 * (4 * p) = 8 * p by omega]
        exact (hcoprime.pow_left 3).mul_dvd_of_dvd_of_dvd (by omega) hpDvd
      have hper := fib_cast_periodic (hperiod.trans hdiv)
      have hzero : (Nat.fib (k + 3) : ZMod k) = 0 := by
        simpa only [zero_add, Nat.fib_zero, Nat.cast_zero] using hper 0
      have hone : (Nat.fib (k + 4) : ZMod k) = 1 := by
        simpa only [show 1 + (k + 3) = k + 4 by omega, Nat.fib_one, Nat.cast_one] using hper 1
      refine ⟨by omega, ?_⟩
      rwa [show k + 4 = (k + 2) + 2 by omega, Nat.fib_add_two, Nat.cast_add,
        show k + 2 + 1 = k + 3 by omega, hzero, add_zero] at hone
  refine ⟨hresult.1, ?_⟩
  have hcast : (Nat.fib (k + 2) : ZMod k) = ((1 : ℕ) : ZMod k) := by
    simpa only [Nat.cast_one] using hresult.2
  simpa only [Nat.mod_eq_of_lt hk] using
    (ZMod.natCast_eq_natCast_iff' (Nat.fib (k + 2)) 1 k).mp hcast

end MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

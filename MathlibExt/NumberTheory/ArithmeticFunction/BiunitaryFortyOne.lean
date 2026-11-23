/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor
import MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution
import MathlibExt.NumberTheory.PrimitivePrimeDivisorPowAddOne
import Mathlib.Tactic.IntervalCases

/-!
# Prime divisors of the biunitary divisor sum of powers of 41

For every positive exponent, the biunitary divisor sum of the corresponding power of 41
has a prime factor outside the set `{2, 3, 5, 13}`.
-/

namespace MetaMathlibExt

open Finset

namespace exists_prime_dvd_sigmaBiunitary_fortyOne_pow

private theorem biunitary_pow_iff {p g i : ℕ} (hp : p.Prime) (hg : 0 < g) (hi : i ≤ g) :
    gcdUnitary (p ^ i) (p ^ g / p ^ i) = 1 ↔ 2 * i ≠ g := by
  rw [Nat.pow_div hi hp.pos]
  constructor
  · intro h hmid
    have he : g - i = i := by omega
    have hmem : p ^ i ∈ (p ^ i).unitaryDivisors := by simp [Nat.unitaryDivisors_prime_pow hp]
    rw [he] at h
    have hle := le_gcdUnitary hmem hmem
    rw [h] at hle
    exact (Nat.one_lt_pow (by omega : i ≠ 0) hp.one_lt).not_ge hle
  · intro hmid
    obtain ⟨h₁, h₂⟩ := gcdUnitary_mem_unitaryDivisors
      (pow_ne_zero i hp.ne_zero) (pow_ne_zero (g - i) hp.ne_zero)
    simp only [Nat.unitaryDivisors_prime_pow hp, mem_insert, mem_singleton] at h₁ h₂
    rcases h₁ with h | h
    · exact h
    rcases h₂ with h' | h'
    · exact h'
    have he := Nat.pow_right_injective hp.two_le (h.symm.trans h')
    omega

-- Pair the lower block of exponents with its translate by n, skipping the middle when g is even.
private theorem pow_add_one_dvd_sum {p : ℕ} (hp : p.Prime) (g : ℕ) (hg : 0 < g) :
    p ^ (g / 2 + 1) + 1 ∣ sigmaBiunitary (p ^ g) := by
  let n := g / 2 + 1
  let k := (g + 1) / 2
  have hsplit : g + 1 = n + k := by dsimp [n, k]; omega
  have hblocks : n = k ∨ n = k + 1 := by dsimp [n, k]; omega
  let f (i : ℕ) := if 2 * i = g then 0 else p ^ i
  have hsum : sigmaBiunitary (p ^ g) = ∑ i ∈ range (g + 1), f i := by
    rw [sigmaBiunitary, biunitaryDivisors, sum_filter, Nat.sum_divisors_prime_pow hp]
    apply sum_congr rfl
    intro i hi
    simp [biunitary_pow_iff hp hg (Nat.le_of_lt_succ (mem_range.mp hi)), f, ite_not]
  have low : ∑ i ∈ range k, f i = ∑ i ∈ range k, p ^ i := by
    apply sum_congr rfl
    intro i hi
    have := mem_range.mp hi
    simp [f, show 2 * i ≠ g by omega]
  have lowBlock : ∑ i ∈ range n, f i = ∑ i ∈ range k, p ^ i := by
    rcases hblocks with h | h
    · rwa [h]
    · rw [h, sum_range_succ, low]
      simp [f, show 2 * k = g by omega]
  refine ⟨∑ i ∈ range k, p ^ i, ?_⟩
  change sigmaBiunitary (p ^ g) = (p ^ n + 1) * _
  rw [hsum, hsplit, sum_range_add, lowBlock, add_mul, one_mul, add_comm, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  simp [f, show 2 * (n + i) ≠ g by omega, pow_add]

private theorem prime_dvd_pow_add_one (n : ℕ) (hn : 1 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ q ∣ 41 ^ n + 1 ∧ q ∉ ({2, 3, 5, 13} : Finset ℕ) := by
  by_cases hsmall : n ≤ 6
  · interval_cases n
    all_goals first
      | exact ⟨7, by decide, by decide, by decide⟩
      | exact ⟨29, by decide, by decide, by decide⟩
      | exact ⟨137, by decide, by decide, by decide⟩
  obtain ⟨q, hq, hmod⟩ := exists_primitivePrimeDivisor_pow_add_one 41 n (by decide) hn
    (by omega) (by omega)
  have hlarge : 13 < q := by
    by_contra! h
    rw [Nat.mod_eq_of_lt (by omega : q < 2 * n)] at hmod
    have := hq.two_le
    omega
  refine ⟨q, hq.prime, ?_, ?_⟩
  · exact_mod_cast hq.dvd
  · simp only [mem_insert, mem_singleton]
    omega

end exists_prime_dvd_sigmaBiunitary_fortyOne_pow

open exists_prime_dvd_sigmaBiunitary_fortyOne_pow

/-- **Prime factors of the biunitary divisor sum of $41^g$.** For every integer $g \ge 1$, the
biunitary divisor sum $\sigma^{**}(41^g)$ has a prime factor $q$ with $q \notin \{2, 3, 5, 13\}$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (V) (`jis-2025-25.4.5-lem-8`). -/
public theorem exists_prime_dvd_sigmaBiunitary_fortyOne_pow (g : ℕ) (hg : 1 ≤ g) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (41 ^ g) ∧ q ∉ ({2, 3, 5, 13} : Finset ℕ) := by
  obtain ⟨q, hq, hdvd, hout⟩ := prime_dvd_pow_add_one (g / 2 + 1) (by omega)
  exact ⟨q, hq, hdvd.trans (pow_add_one_dvd_sum (by decide) g hg), hout⟩

end MetaMathlibExt

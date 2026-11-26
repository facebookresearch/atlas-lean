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

/-!
# Prime factors at least `5` of biunitary divisor sums of prime powers

This module proves that for every prime `p` and every `g ≥ 2` with `(p, g) ≠ (2, 4)`, the
biunitary divisor sum `σ**(p ^ g)` has a prime factor `q ≥ 5`
(`MetaMathlibExt.exists_prime_ge_five_dvd_sigmaBiunitary_prime_pow`). The proof factors
`σ**(p ^ g)` through `p ^ u + 1` with `u = g / 2 + 1` and applies the Bang–Zsigmondy
primitive prime divisor lemma for `a ^ n + 1`, whose prime is `1` modulo `2 * u`; the case
`(p, g) = (2, 5)` is checked directly.

Statements from Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain
Form*, Journal of Integer Sequences 28 (2025), Article 25.4.5.

Following Wall (as quoted in the paper's introduction), a divisor `d` of `n` is biunitary when
`gcd₁(d, n / d) = 1`, where `gcd₁(a, b)` is the greatest common unitary divisor of `a` and `b`
(a unitary divisor of `a` is a divisor `d` with `gcd(d, a / d) = 1`, `Nat.unitaryDivisors`).
The paper's `σ**(n)` is `MetaMathlibExt.sigmaBiunitary n`.
-/

namespace MetaMathlibExt

open Finset

namespace exists_prime_ge_five_dvd_sigmaBiunitary_prime_pow

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

/-- Every power up to the given exponent occurs except the middle one. -/
private theorem sigmaBiunitary_prime_pow_eq_sum {p g : ℕ} (hp : p.Prime) (hg : 0 < g) :
    sigmaBiunitary (p ^ g) = ∑ i ∈ range (g + 1), if 2 * i = g then 0 else p ^ i := by
  rw [sigmaBiunitary, biunitaryDivisors, sum_filter, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro i hi
  simp [biunitary_pow_iff hp hg (Nat.le_of_lt_succ (mem_range.mp hi)), ite_not]

-- Pair the lower block of exponents with its translate by n, skipping the middle when g is even.
private theorem pow_add_one_dvd_sum {p : ℕ} (hp : p.Prime) (g : ℕ) (hg : 0 < g) :
    p ^ (g / 2 + 1) + 1 ∣ sigmaBiunitary (p ^ g) := by
  let n := g / 2 + 1
  let k := (g + 1) / 2
  have hsplit : g + 1 = n + k := by dsimp [n, k]; omega
  have hblocks : n = k ∨ n = k + 1 := by dsimp [n, k]; omega
  let f (i : ℕ) := if 2 * i = g then 0 else p ^ i
  have hsum : sigmaBiunitary (p ^ g) = ∑ i ∈ range (g + 1), f i :=
    sigmaBiunitary_prime_pow_eq_sum hp hg
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

end exists_prime_ge_five_dvd_sigmaBiunitary_prime_pow

open exists_prime_ge_five_dvd_sigmaBiunitary_prime_pow

/-- **Prime factors at least $5$ of biunitary divisor sums of prime powers.** For every prime $p$
and every integer $g \ge 2$ with $(p, g) \ne (2, 4)$, the biunitary divisor sum $\sigma^{**}(p^g)$
has a prime factor $q \ge 5$.

The excluded case is a genuine exception: $\sigma^{**}(2^4) = 1 + 2 + 8 + 16 = 27 = 3^3$. It is
not in the printed statement; the paper's proof applies Lemma 2.4 to $p^u + 1$ with
$g = 2u - 1 - \varepsilon$, and $(p, u) = (2, 3)$ is that lemma's exception.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (I) (`jis-2025-25.4.5-lem-8`). -/
public theorem exists_prime_ge_five_dvd_sigmaBiunitary_prime_pow (p g : ℕ)
    (hp : p.Prime) (hg : 2 ≤ g) (hexc : ¬ (p = 2 ∧ g = 4)) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (p ^ g) ∧ 5 ≤ q := by
  by_cases h25 : p = 2 ∧ g = 5
  · obtain ⟨rfl, rfl⟩ := h25
    exact ⟨7, by decide, by decide, by decide⟩
  · have hexc1 : ¬ (p = 2 ∧ g / 2 + 1 = 3) := by
      rintro ⟨rfl, h⟩
      have hg45 : g = 4 ∨ g = 5 := by omega
      rcases hg45 with rfl | rfl
      · exact hexc ⟨rfl, rfl⟩
      · exact h25 ⟨rfl, rfl⟩
    obtain ⟨q, hq, hmod⟩ := exists_primitivePrimeDivisor_pow_add_one p (g / 2 + 1)
      hp.two_le (by omega) hexc1 (by omega)
    have hdvd : q ∣ p ^ (g / 2 + 1) + 1 := by exact_mod_cast hq.dvd
    have hq2 := hq.two_le
    have h2u : 2 * (g / 2 + 1) ≤ q := by
      by_contra h
      rw [Nat.mod_eq_of_lt (by omega : q < 2 * (g / 2 + 1))] at hmod
      omega
    have hne : q ≠ 2 * (g / 2 + 1) := by
      rintro rfl
      rw [Nat.mod_self] at hmod
      omega
    have h5 : 5 ≤ q := by omega
    exact ⟨q, hq.prime, hdvd.trans (pow_add_one_dvd_sum hp g (by omega)), h5⟩

end MetaMathlibExt

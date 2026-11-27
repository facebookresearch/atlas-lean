/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Primitive non-deficient numbers of the form `2 ^ a * p`

For an odd prime `p`, the primitive non-deficient numbers of this form are exactly those
with `2 ^ a < p ≤ 2 ^ (a + 1) - 1`.
-/

public section

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

/-- **Even primitive non-deficient numbers with two prime factors.** Let $p$ be an odd prime and
$a$ a natural number. Then $2^a p$ is primitive non-deficient if and only if
$2^a < p \le 2^{a+1} - 1$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `Classificationofprimitivenondeficientwhenkis2`), first
part. -/
theorem isPrimitiveNondeficient_two_pow_mul_prime_iff
    (a p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) :
    IsPrimitiveNondeficient (2 ^ a * p) ↔
      2 ^ a < p ∧ p ≤ 2 ^ (a + 1) - 1 := by
  have htwo (k : ℕ) : (∑ d ∈ (2 ^ k).divisors, d) + 1 = 2 * 2 ^ k := by
    rw [Nat.sum_divisors_prime_pow Nat.prime_two, ← pow_succ']
    simpa using geom_sum_mul_add (1 : ℕ) (k + 1)
  have hc := (Nat.coprime_primes Nat.prime_two hp).mpr hpo.symm
  have hsum_iff (k : ℕ) :
      2 * (2 ^ k * p) ≤ ∑ d ∈ (2 ^ k * p).divisors, d ↔ p < 2 ^ (k + 1) := by
    rw [(hc.pow_left k).sum_divisors_mul, hp.sum_divisors, pow_succ', ← mul_assoc,
      ← htwo, add_mul, one_mul, mul_add, mul_one]
    omega
  constructor
  · rintro ⟨⟨_, hsum⟩, hproper⟩
    have hupper := (hsum_iff a).mp hsum
    refine ⟨?_, by omega⟩
    cases a with
    | zero => simpa using hp.one_lt
    | succ k =>
      -- Removing a single factor of two gives a deficient proper divisor.
      rw [pow_succ', mul_assoc] at hproper
      have hpos : 0 < 2 ^ k * p := Nat.mul_pos (by positivity) hp.pos
      have hdef := hproper (2 ^ k * p)
        (Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, by positivity⟩) (by omega)
      have hle : 2 ^ (k + 1) ≤ p := le_of_not_gt (mt (hsum_iff k).mpr hdef.not_ge)
      obtain ⟨t, ht⟩ := hp.odd_of_ne_two hpo
      rw [pow_succ'] at hle ⊢
      omega
  · rintro ⟨hlo, hhi⟩
    have hp0 := hp.pos
    refine ⟨⟨Nat.mul_ne_zero (by positivity) hp.ne_zero, (hsum_iff a).mpr (by omega)⟩, ?_⟩
    intro m hm hlt
    -- The divisor is either a power of two or that power multiplied by the full prime.
    obtain ⟨u, v, hu, hv, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.dvd_of_mem_divisors hm)
    obtain ⟨k, hka, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
    rcases (Nat.dvd_prime hp).mp hv with rfl | rfl
    · simp only [mul_one]
      have := htwo k
      omega
    · have hk : k < a := hka.lt_of_ne (fun h => by subst k; exact hlt.false)
      have hpow : 2 ^ (k + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) hk
      exact lt_of_not_ge (mt (hsum_iff k).mp (hpow.trans_lt hlo).not_gt)

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted

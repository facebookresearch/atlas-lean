/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.CompletelyAdditiveHeight

/-! # Tests for completely additive heights and the ordinary partition profile -/

open MetaMathlibExt

-- The product range is empty at level one.
example {H : ℕ → ℕ} (hH : IsHeightFunction H) :
    {m : ℕ | 0 < m ∧ H m = 1} = {p : ℕ | p.Prime ∧ H p = 1} := by
  rw [heightLevel_eq_products_union_primes hH (by decide : 1 ≤ 1)]
  ext m
  constructor
  · rintro (⟨ℓ, hpos, hbound, _⟩ | hp)
    · omega
    · exact hp
  · exact Or.inr

-- A prime square attains the upper bound on the height of the extracted factor.
example {H : ℕ → ℕ} (hH : IsHeightFunction H) {p : ℕ} (hp : p.Prime) :
    p ^ 2 ∈ {m : ℕ | 0 < m ∧ H m = 2 * H p} := by
  have hpH := hH.prime_pos p hp
  rw [heightLevel_eq_products_union_primes hH (by omega : 1 ≤ 2 * H p)]
  exact Or.inl ⟨H p, hpH, by omega, p, p, hp, rfl, hp.pos, by omega, pow_two p⟩

-- The profile starts at level one, even when its unused zeroth entry is nonzero.
example (a : ℕ) : profilePartialSum (fun k => if k = 0 then a else 1) 0 = 0 := by
  simp [profilePartialSum]

-- An unattained positive index uses the empty-set value.
example : seqHeightIndex (fun _ => 0) 1 = 0 := by
  simp [seqHeightIndex, profilePartialSum]

-- At the first allowed index, the strict lower bound is tight by one.
example : nthPrimeOne 6 - 2 * 6 = 1 := by
  have hl := two_mul_lt_nthPrimeOne (k := 6) (by decide)
  have hu : nthPrimeOne 6 < 14 :=
    Nat.nth_lt_of_lt_count (by decide : 5 < Nat.count Nat.Prime 14)
  omega

-- At the prime-square endpoint, 2 divides two terms and 4 contributes once more.
example {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    ∑ m ∈ Finset.Icc 1 4, H m = 3 * H 2 + H 3 := by
  rw [sum_height_eq_sum_prime_powers hH (by decide),
    show (Finset.Iic 4).filter Nat.Prime = {2, 3} by decide,
    Finset.sum_pair (by decide)]
  rw [show (Finset.Icc 1 4).filter (fun a => 2 ^ a ≤ 4) = {1, 2} by decide,
    show (Finset.Icc 1 4).filter (fun a => 3 ^ a ≤ 4) = {1} by decide,
    Finset.sum_pair (by decide), Finset.sum_singleton]
  simp
  omega

-- The one-based prime labels used as weights apply to every prime in the sequence.
example (i : ℕ) : canonicalSeqHeight (fun _ => 1) (nthPrimeOne (i + 1)) = i + 1 := by
  simp only [canonicalSeqHeight, nthPrimeOne, Nat.add_sub_cancel,
    additiveOfPrimeValues_prime _ (Nat.prime_nth_prime i), seqHeightIndex_const_one]
  exact congrArg (· + 1) (Nat.primeCounting'_nth_eq i)

-- Multiplicity matters: 12 has two factors of height one and one factor of height two.
example : canonicalSeqHeight (fun _ => 1) 12 = 4 := by
  unfold canonicalSeqHeight
  rw [show 12 = 2 * (2 * 3) by decide]
  rw [isCompletelyAdditiveNat_additiveOfPrimeValues _ 2 6 (by decide) (by decide),
    isCompletelyAdditiveNat_additiveOfPrimeValues _ 2 3 (by decide) (by decide),
    additiveOfPrimeValues_prime _ Nat.prime_two, additiveOfPrimeValues_prime _ Nat.prime_three]
  simp only [seqHeightIndex_const_one]
  decide

-- Matula iteration starts at eight when the iteration count truncates to zero.
example : matulaMax 2 = 8 := rfl

-- The ordinary partition coefficient at two counts 2 and 1+1.
example : weightedPartitionCoeff (fun _ => 1) 2 = 2 := by
  rw [weightedPartitionCoeff.eq_2, Fin.sum_univ_two]
  norm_num [Nat.prime_two.divisors, weightedPartitionCoeff_zero,
    weightedPartitionCoeff_one]

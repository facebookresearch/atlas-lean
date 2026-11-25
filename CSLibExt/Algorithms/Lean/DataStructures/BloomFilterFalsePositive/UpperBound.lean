/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BloomFilterFalsePositive

/-!
# Bloom filters: elementary upper bound on the false-positive rate

For at least one hash function, the exact false-positive rate is at most the expected
fraction of set bits `1 - (1 - 1/m) ^ (n * k)`, since each summand satisfies
`t ^ k ≤ t` for `t ∈ [0, 1]`. Also covers the degenerate cases: with no stored
elements the rate is zero, and with no hash functions every query is vacuously positive.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.BloomFilter

open Finset

section Uniform

variable {m n k : ℕ}

/-- **Elementary upper bound** on the false-positive rate: for at least one
hash function, the exact rate is at most the expected fraction of set bits
`1 - (1 - 1/m) ^ (n * k)`. -/
theorem falsePositiveProb_le (hm : 0 < m) (hk : 1 ≤ k) :
    falsePositiveProb m n k ≤ 1 - (1 - 1 / (m : ℝ)) ^ (n * k) := by
  rw [falsePositiveProb_eq hm, ← expected_fraction_set hm]
  have hN : 0 < (Fintype.card (Fin n → Fin k → Fin m) : ℝ) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    positivity
  rw [div_le_div_iff_of_pos_right hN]
  apply Finset.sum_le_sum
  intro H _
  apply pow_le_of_le_one
  · positivity
  · rw [div_le_one (by positivity : (0 : ℝ) < m)]
    have hcard : #(setBits H) ≤ m := by
      calc #(setBits H) ≤ Fintype.card (Fin m) := Finset.card_le_univ _
        _ = m := Fintype.card_fin m
    exact_mod_cast hcard
  · omega

/-- With no stored elements and at least one hash function, the
false-positive rate is zero. -/
theorem falsePositiveProb_zero_stored (hm : 0 < m) (hk : 1 ≤ k) :
    falsePositiveProb m 0 k = 0 := by
  have hle := falsePositiveProb_le (m := m) (n := 0) (k := k) hm hk
  simp only [zero_mul, pow_zero, sub_self] at hle
  have hnn : 0 ≤ falsePositiveProb m 0 k := by
    unfold falsePositiveProb
    positivity
  exact le_antisymm hle hnn

/-- With no hash functions, every query is a (vacuous) false positive. -/
theorem falsePositiveProb_zero_hashes [NeZero m] : falsePositiveProb m n 0 = 1 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [falsePositiveProb_eq hm]
  simp only [pow_zero]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : (Fintype.card (Fin n → Fin 0 → Fin m) : ℝ) ≠ 0 := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    positivity
  rw [div_self hcard]

end Uniform

end Cslib.Algorithms.Lean.BloomFilter

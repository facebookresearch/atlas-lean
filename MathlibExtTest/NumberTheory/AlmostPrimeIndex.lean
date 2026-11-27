/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlmostPrimeIndex
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.SumPrimeReciprocals

namespace MetaMathlibExt.AlmostPrimeIndex

private theorem one_factor_eq_prime : Nat.IsAlmostPrime 1 = Nat.Prime :=
  funext fun _ ↦ propext Nat.isAlmostPrime_one_iff

-- The only zero-almost prime is 1. Two rounds of prime indexing send 1 to 2 to 3.
example : almostPrimeIndexSet 1 [1, 0] = {3} := by
  ext n
  simp [almostPrimeIndexSet, one_factor_eq_prime]

-- With a prime as the last index, 2 gives the chain 2, 3, 5.
private theorem five_mem_one_one : 5 ∈ almostPrimeIndexSet 1 [1, 1] := by
  refine ⟨3, ⟨2, Nat.prime_two.isAlmostPrime_one, by decide, ?_⟩, by decide, ?_⟩
  · exact one_factor_eq_prime ▸ Nat.nth_prime_one_eq_three.symm
  · exact one_factor_eq_prime ▸ Nat.nth_prime_two_eq_five.symm

-- The case `m = 2`: the `j`-almost primes of `k`-almost prime index.
example {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    Summable fun n : almostPrimeIndexSet j [k] => (1 : ℝ) / n :=
  summable_inv_almostPrimeIndexSet hj (List.cons_ne_nil _ _) (by simpa using hk)

-- Summability makes the sum genuine (not the junk value `0`): it dominates the term `1 / 5`.
example : (1 : ℝ) / 5 ≤ ∑' n : almostPrimeIndexSet 1 [1, 1], (1 : ℝ) / n := by
  have hs := summable_inv_almostPrimeIndexSet (k := 1) (L := [1, 1]) le_rfl (by simp) (by simp)
  exact_mod_cast hs.le_tsum ⟨5, five_mem_one_one⟩ fun _ _ ↦ by positivity

-- The index list must be nonempty: the reciprocal sum of the primes diverges.
example : ¬ Summable fun n : almostPrimeIndexSet 1 [] => (1 : ℝ) / n := by
  have h : almostPrimeIndexSet 1 [] = {p | p.Prime} := by
    simp [almostPrimeIndexSet]
  rw [h]
  exact summable_subtype_iff_indicator.not.mpr not_summable_one_div_on_primes

end MetaMathlibExt.AlmostPrimeIndex

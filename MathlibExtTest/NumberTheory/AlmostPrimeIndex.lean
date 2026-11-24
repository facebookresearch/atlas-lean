/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlmostPrimeIndex
import Mathlib.Data.Nat.Prime.Nth

namespace MetaMathlibExt.AlmostPrimeIndex

private theorem one_factor_eq_prime : Nat.IsAlmostPrime 1 = Nat.Prime :=
  funext fun _ ↦ propext Nat.isAlmostPrime_one_iff

-- The only zero-almost prime is 1. Two rounds of prime indexing send 1 to 2 to 3.
example : almostPrimeIndexSet 1 [1, 0] = {3} := by
  ext n
  simp [almostPrimeIndexSet, one_factor_eq_prime]

-- With a prime as the last index, 2 gives the chain 2, 3, 5.
example : 5 ∈ almostPrimeIndexSet 1 [1, 1] := by
  refine ⟨3, ⟨2, Nat.prime_two.isAlmostPrime_one, by decide, ?_⟩, by decide, ?_⟩
  · exact one_factor_eq_prime ▸ Nat.nth_prime_one_eq_three.symm
  · exact one_factor_eq_prime ▸ Nat.nth_prime_two_eq_five.symm

end MetaMathlibExt.AlmostPrimeIndex

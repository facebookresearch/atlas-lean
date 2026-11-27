/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.PadicInt

open MetaMathlibExt

-- The least positive index, for any element of the ideal.
example (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) (ha : a ∈ Ideal.span {(p : ℤ_[p])}) :
    ∃ c ∈ Ideal.span {(p : ℤ_[p])}, a = c := by
  simpa only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] using
    isDividedPowerIdeal_span_prime_padicInt p a ha 1 le_rfl

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- The generator at index two, where the factorial is not a unit.
example : ∃ c ∈ Ideal.span {(2 : ℤ_[2])}, (2 : ℤ_[2]) ^ 2 = (2 : ℤ_[2]) * c := by
  have hp : (2 : ℤ_[2]) ∈ Ideal.span {(2 : ℤ_[2])} := Ideal.subset_span (Set.mem_singleton _)
  exact isDividedPowerIdeal_span_prime_padicInt 2 2 hp 2 (by decide)

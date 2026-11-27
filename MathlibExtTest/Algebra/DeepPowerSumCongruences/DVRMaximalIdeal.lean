/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.DVRMaximalIdeal
import Mathlib.NumberTheory.Padics.PadicIntegers

open MetaMathlibExt

-- The prime 2 in ℤ₂ attains equality in the ramification bound.
section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

example : IsDividedPowerIdeal (IsLocalRing.maximalIdeal ℤ_[2]) := by
  have he : Ideal.span {((2 : ℕ) : ℤ_[2])} = IsLocalRing.maximalIdeal ℤ_[2] ^ 1 := by
    rw [pow_one, PadicInt.maximalIdeal_eq_span_p]
  exact (isDividedPowerIdeal_maximalIdeal_iff (p := 2) (by decide) he).2 (by decide)

end

-- At ramification index 2 over the same prime, the bound fails.
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (he : Ideal.span {((2 : ℕ) : O)} = IsLocalRing.maximalIdeal O ^ 2) :
    ¬ IsDividedPowerIdeal (IsLocalRing.maximalIdeal O) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isDividedPowerIdeal_maximalIdeal_iff (p := 2) (by decide) he).not.mpr (by decide)

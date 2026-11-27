/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.DVRMaximalIdealPow

open MetaMathlibExt

section

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

-- For ramification index 4 at p = 3, the square attains the bound but the maximal ideal does not.
example (he : Ideal.span {((3 : ℕ) : O)} = IsLocalRing.maximalIdeal O ^ 4) :
    IsDividedPowerIdeal (IsLocalRing.maximalIdeal O ^ 2) ∧
      ¬ IsDividedPowerIdeal (IsLocalRing.maximalIdeal O) := by
  refine ⟨(isDividedPowerIdeal_maximalIdeal_pow_iff (p := 3) (by decide) he 2).2 (by decide), ?_⟩
  simpa only [pow_one] using
    (isDividedPowerIdeal_maximalIdeal_pow_iff (p := 3) (by decide) he 1).not.mpr (by decide)

end

-- The zeroth power is the unit ideal and fails the criterion for every positive e.
example {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {e : ℕ} (he0 : e ≠ 0) (he : Ideal.span {(p : O)} = IsLocalRing.maximalIdeal O ^ e) :
    ¬ IsDividedPowerIdeal (⊤ : Ideal O) := by
  simpa only [pow_zero, Ideal.one_eq_top] using
    (isDividedPowerIdeal_maximalIdeal_pow_iff he0 he 0).not.mpr (by simpa using he0)

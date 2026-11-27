/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.NatCardQuotientMaximalIdealPow

@[expose] public section

-- Consumer with the original binders.
example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ) :
    Nat.card (R ⧸ IsLocalRing.maximalIdeal R ^ n) =
      Nat.card (IsLocalRing.ResidueField R) ^ n :=
  IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow n

-- Boundary case `n = 0`: the quotient by `𝔪 ^ 0 = ⊤` is a subsingleton, so
-- its cardinality is `1`, matching `Nat.card k ^ 0 = 1` for any residue
-- field `k`, finite or infinite.
example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Nat.card (R ⧸ IsLocalRing.maximalIdeal R ^ 0) = 1 := by
  rw [IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, pow_zero]

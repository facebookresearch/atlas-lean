/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.KrullDimLeTwo

open IsLocalRing

/-- Smoke test: the theorem applies with abstract rings. -/
example {B : Type} [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
    {R : Type} [CommRing R] (e : AdicCompletion (maximalIdeal B) B ≃+* R)
    (hR : ringKrullDim R ≤ 2) :
    ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥ :=
  IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two e hR

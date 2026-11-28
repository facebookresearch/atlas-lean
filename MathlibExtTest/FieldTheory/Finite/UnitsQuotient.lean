/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.UnitsQuotient

import Mathlib.FieldTheory.Finite.GaloisField

-- `𝔽₉ˣ / 𝔽₃ˣ` is cyclic of order `4`.
example :
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    IsCyclic ((GaloisField 3 2)ˣ ⧸
        (Units.map (algebraMap (ZMod 3) (GaloisField 3 2) : ZMod 3 →* GaloisField 3 2)).range) ∧
      Nat.card ((GaloisField 3 2)ˣ ⧸
        (Units.map (algebraMap (ZMod 3) (GaloisField 3 2) : ZMod 3 →* GaloisField 3 2)).range) =
        3 + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact FiniteField.isCyclic_units_quotient_and_natCard_eq (Nat.card_zmod 3)
    (GaloisField.card 3 2 two_ne_zero)

-- For any prime `ℓ` and any field `F` with `ℓ²` elements, `Fˣ / 𝔽_ℓˣ` has order `ℓ + 1`.
example {ℓ : ℕ} [Fact ℓ.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod ℓ) F]
    (hF : Nat.card F = ℓ ^ 2) :
    Nat.card (Fˣ ⧸ (Units.map (algebraMap (ZMod ℓ) F : ZMod ℓ →* F)).range) = ℓ + 1 :=
  (FiniteField.isCyclic_units_quotient_and_natCard_eq (Nat.card_zmod ℓ) hF).2

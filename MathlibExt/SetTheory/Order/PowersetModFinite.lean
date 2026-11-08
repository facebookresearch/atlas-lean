/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 351, Logic 352

/-!
# Equal mod finite; $P(\omega)\slash \textrm{fin}$ automorphism

## References

* Jech (for `EqModFinite`, `IsPowModFiniteAutomorphism`)
-/

namespace MetaMathlibExt

-- Logic 351: Equal mod finite

/-- A =^* B (equal mod finite) if the symmetric difference between A and B is finite. -/
def EqModFinite (A B : Set ℕ) : Prop := (symmDiff A B).Finite

-- Logic 352: $P(\omega)\slash \textrm{fin}$ automorphism

/-- Φ is an automorphism of P(ω)/ fin if presented on representatives, it respects =^* (equality
modulo finite),
preserves meets and complements modulo finite, is one-to-one and onto modulo finite.
-/
structure IsPowModFiniteAutomorphism (Φ : Set ℕ → Set ℕ) : Prop where
  respects : ∀ A B : Set ℕ, EqModFinite A B → EqModFinite (Φ A) (Φ B)
  inter : ∀ A B : Set ℕ, EqModFinite (Φ (A ∩ B)) (Φ A ∩ Φ B)
  compl : ∀ A : Set ℕ, EqModFinite (Φ Aᶜ) (Φ A)ᶜ
  injective : ∀ A B : Set ℕ, EqModFinite (Φ A) (Φ B) → EqModFinite A B
  surjective : ∀ B : Set ℕ, ∃ A : Set ℕ, EqModFinite (Φ A) B

end MetaMathlibExt

end

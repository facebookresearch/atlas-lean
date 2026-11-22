/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.AlgHomCardBound
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section

-- Consumer with the original binders.
example
    (R : Type*) [CommRing R] [IsLocalRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (Ω : Type*) [Field Ω] [Algebra R Ω] :
    Finite (B →ₐ[R] Ω) ∧
      Nat.card (B →ₐ[R] Ω) ≤
        Module.finrank (IsLocalRing.ResidueField R)
          (TensorProduct R (IsLocalRing.ResidueField R) B) :=
  Algebra.card_algHom_le_finrank_residueField_tensorProduct R B Ω

-- The finiteness hypothesis matters: without it, there can be infinitely
-- many algebra maps, as evaluation at each rational point shows for
-- `ℚ[X] →ₐ[ℚ] ℚ`.
example : Infinite (Polynomial ℚ →ₐ[ℚ] ℚ) := by
  apply Infinite.of_injective (fun q : ℚ => Polynomial.aeval q)
  intro a b hab
  have h := AlgHom.congr_fun hab Polynomial.X
  simpa using h

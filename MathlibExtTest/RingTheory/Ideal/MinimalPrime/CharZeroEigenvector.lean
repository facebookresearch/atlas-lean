/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.MinimalPrime.CharZeroEigenvector

@[expose] public section

-- Consumer with the original binders.
example {T : Type*} [CommRing T] [Module.Finite ℤ T] [Module.IsTorsionFree ℤ T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module.Finite T M] [FaithfulSMul T M]
    {k : Type*} [Field k] (χ : T →+* k) :
    ∃ 𝔭 ∈ minimalPrimes T,
      𝔭 ≤ RingHom.ker χ ∧
        (∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) ∧
          CharZero (T ⧸ 𝔭) ∧
            (∃ red : T ⧸ 𝔭 →+* k, red.comp (Ideal.Quotient.mk 𝔭) = χ) ∧
              ∃ x : M,
                x ≠ 0 ∧
                  (∀ p ∈ 𝔭, p • x = 0) ∧
                    (∀ (r : T), r • x = 0 → r ∈ 𝔭) ∧
                      ∀ (h h' : T), (Ideal.Quotient.mk 𝔭) h =
                        (Ideal.Quotient.mk 𝔭) h' → h • x = h' • x :=
  DeligneSerre.exists_charZero_eigenvector_of_residual_character χ

-- Higher-universe consumer for the module.
example {T : Type*} [CommRing T] [Module.Finite ℤ T] [Module.IsTorsionFree ℤ T]
    {M : Type 1} [AddCommGroup M] [Module T M] [Module.Finite T M] [FaithfulSMul T M]
    {k : Type*} [Field k] (χ : T →+* k) :
    ∃ 𝔭 ∈ minimalPrimes T,
      𝔭 ≤ RingHom.ker χ ∧
        (∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) ∧
          CharZero (T ⧸ 𝔭) ∧
            (∃ red : T ⧸ 𝔭 →+* k, red.comp (Ideal.Quotient.mk 𝔭) = χ) ∧
              ∃ x : M,
                x ≠ 0 ∧
                  (∀ p ∈ 𝔭, p • x = 0) ∧
                    (∀ (r : T), r • x = 0 → r ∈ 𝔭) ∧
                      ∀ (h h' : T), (Ideal.Quotient.mk 𝔭) h =
                        (Ideal.Quotient.mk 𝔭) h' → h • x = h' • x :=
  DeligneSerre.exists_charZero_eigenvector_of_residual_character χ

-- Boundary: in characteristic `p`, the integer hypothesis fails, so the
-- characteristic-zero conclusion cannot hold for `ZMod p`.
example (p : ℕ) (hp : 0 < p) : ¬ CharZero (ZMod p) := by
  intro h
  have hinj : Function.Injective ((↑) : ℕ → ZMod p) := Nat.cast_injective
  apply hp.ne'
  apply hinj
  simp [CharP.cast_eq_zero (R := ZMod p) (p := p)]

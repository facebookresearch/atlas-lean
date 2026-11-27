/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Jacobson.CharZeroFiniteType

@[expose] public section

universe u

/-- Consumer with the original binders, restated over `Type*`. -/
example (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    ∃ (p₁ p₂ : ℕ) (𝔪₁ 𝔪₂ : Ideal A), p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      𝔪₁.IsMaximal ∧ 𝔪₂.IsMaximal ∧ (p₁ : A) ∈ 𝔪₁ ∧ (p₂ : A) ∈ 𝔪₂ :=
  Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero

/-- Higher-universe consumer. -/
example (A : Type u) [CommRing A] [IsDomain A] [CharZero A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    ∃ (p₁ p₂ : ℕ) (𝔪₁ 𝔪₂ : Ideal A), p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      𝔪₁.IsMaximal ∧ 𝔪₂.IsMaximal ∧ (p₁ : A) ∈ 𝔪₁ ∧ (p₂ : A) ∈ 𝔪₂ :=
  Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero

/-- Boundary example: `ℤ` itself, of finite type over `ℤ` in characteristic
zero, has the two maximal ideals `(2)` and `(3)`. -/
example :
    ∃ (p₁ p₂ : ℕ) (𝔪₁ 𝔪₂ : Ideal ℤ), p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      𝔪₁.IsMaximal ∧ 𝔪₂.IsMaximal ∧ (p₁ : ℤ) ∈ 𝔪₁ ∧ (p₂ : ℤ) ∈ 𝔪₂ :=
  Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero (A := ℤ)

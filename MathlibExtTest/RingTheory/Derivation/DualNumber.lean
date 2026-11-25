/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Derivation.DualNumber
public import Mathlib.Algebra.Polynomial.Derivation

@[expose] public section

/-- Consumer with the source's binders: a point `φ₀` and a function `D` that is additive, Leibniz
over `φ₀` and compatible with the scalars of `A` package into a `Derivation` over the
`B`-algebra structure that `φ₀` puts on `Ω`. -/
example {A B Ω : Type*} [CommRing A] [CommRing B] [Field Ω]
    [Algebra A B] [Algebra A Ω]
    (φ₀ : B →ₐ[A] Ω) (D : B → Ω)
    (hDadd : ∀ x y : B, D (x + y) = D x + D y)
    (hDmul : ∀ x y : B, D (x * y) = φ₀ x * D y + D x * φ₀ y)
    (hDA : ∀ (a : A) (x : B), D (algebraMap A B a * x) = algebraMap A Ω a * D x)
    (hD : ∃ b : B, D b ≠ 0) :
    ∃ φ : B →ₐ[A] DualNumber Ω,
      (∀ b : B, (φ b).fst = φ₀ b) ∧ ∃ b : B, (φ b).snd ≠ 0 := by
  let : Algebra B Ω := φ₀.toRingHom.toAlgebra
  have : IsScalarTower A B Ω := IsScalarTower.of_algebraMap_eq fun a => (φ₀.commutes a).symm
  let D' : Derivation A B Ω :=
    Derivation.mk'
      { toFun := D
        map_add' := hDadd
        map_smul' := fun a x => by simpa [Algebra.smul_def] using hDA a x }
      fun x y => by
        simp [hDmul, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm, add_comm]
  exact D'.exists_algHom_dualNumber_fst_eq_snd_ne_zero hD

/-- Concrete boundary example: over the first projection of the dual numbers over `ℚ`, the second
projection is a derivation, nonzero at `ε`. -/
example :
    ∃ φ : DualNumber ℚ →ₐ[ℚ] DualNumber ℚ,
      (∀ b : DualNumber ℚ, (φ b).fst = b.fst) ∧
        ∃ b : DualNumber ℚ, (φ b).snd ≠ 0 := by
  let : Algebra (DualNumber ℚ) ℚ := TrivSqZeroExt.algebraBase ℚ ℚ
  let D : Derivation ℚ (DualNumber ℚ) ℚ :=
    Derivation.mk' (TrivSqZeroExt.sndHom ℚ ℚ) fun x y => by
      change (x * y).snd = x.fst * y.snd + y.fst * x.snd
      rw [DualNumber.snd_mul, mul_comm x.snd]
  exact D.exists_algHom_dualNumber_fst_eq_snd_ne_zero ⟨DualNumber.eps, by simp [D]⟩

open Polynomial in
/-- A consumer over a ring that is not a field: `ℤ` is a `ℤ[X]`-algebra through evaluation at
zero, and the formal derivative evaluated at zero, `p ↦ p'(0)`, is a derivation, nonzero at `X`. -/
example :
    ∃ φ : ℤ[X] →ₐ[ℤ] DualNumber ℤ,
      (∀ p : ℤ[X], (φ p).fst = p.eval 0) ∧ ∃ p : ℤ[X], (φ p).snd ≠ 0 := by
  let : Algebra ℤ[X] ℤ := (evalRingHom 0).toAlgebra
  let D : Derivation ℤ ℤ[X] ℤ := mkDerivation ℤ (1 : ℤ)
  have hD (p : ℤ[X]) : D p = (derivative p).eval 0 := by
    simp [D, mkDerivation_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  exact D.exists_algHom_dualNumber_fst_eq_snd_ne_zero ⟨X, by simp [hD]⟩

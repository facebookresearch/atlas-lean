/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

open AlgebraicCurve
open scoped Pointwise

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

example (v : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n * v.deg :=
  Divisor.degree_single v n

example (D : Divisor K F) :
    D ∈ Divisor.degZero (K := K) (F := F) ↔ Divisor.degree D = 0 :=
  Divisor.mem_degZero

/-! The torsion count `AbelJacobiCard`, stated with Mathlib's `AddSubgroup.torsionBy`. -/

example (p g : ℕ) :
    AbelJacobiCard K F p g ↔ p.Prime ∧
      ∀ n : ℕ, Nat.card (AddSubgroup.torsionBy (Pic0 K F) (p ^ n : ℕ)) = p ^ (2 * g * n) :=
  Iff.rfl

example (n : ℕ) (x : Pic0 K F) : x ∈ AddSubgroup.torsionBy (Pic0 K F) (n : ℤ) ↔ n • x = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

/-- The degenerate exponent `p = 1`, for which the count holds trivially, is excluded. -/
example (g : ℕ) : ¬ AbelJacobiCard K F 1 g := fun h => Nat.not_prime_one h.1

/-- For a prime `p` the count forces every `p ^ n`-torsion subgroup to be finite. -/
example (p g n : ℕ) (h : AbelJacobiCard K F p g) :
    Finite (AddSubgroup.torsionBy (Pic0 K F) (p ^ n : ℕ)) :=
  Nat.finite_of_card_ne_zero (by rw [h.2 n]; exact (pow_pos h.1.pos _).ne')

/-! The action of `F ≃ₐ[K] F` on places. -/

example (σ : F ≃ₐ[K] F) (A : ValuationSubring F) (x : A) :
    ((Place.smulRingEquiv σ A x : (σ • A : ValuationSubring F)) : F) = σ x :=
  rfl

/-- The action on places is the transport of `Curve/PlaceCongr.lean` along `σ`. -/
example (σ : F ≃ₐ[K] F) (v : Place K F) : σ • v = Place.congrRingEquiv σ.toRingEquiv σ.commutes v :=
  rfl

example (σ : F ≃ₐ[K] F) (v : Place K F) :
    Place.smulResidueAlgEquiv σ v = Place.congrResidueAlgEquiv σ.toRingEquiv σ.commutes v :=
  rfl

/-- The valuation subring of `σ • v` is the image of that of `v` under `σ`. -/
example (σ : F ≃ₐ[K] F) (v : Place K F) :
    (σ • v).toValuationSubring = σ • v.toValuationSubring :=
  Place.smul_toValuationSubring σ v

example (σ : F ≃ₐ[K] F) (v : Place K F) (x : F) :
    x ∈ (σ • v).toValuationSubring ↔ σ.symm x ∈ v.toValuationSubring :=
  Iff.rfl

example (v : Place K F) : (1 : F ≃ₐ[K] F) • v = v := one_smul _ v

example (σ τ : F ≃ₐ[K] F) (v : Place K F) : (σ * τ) • v = σ • τ • v := mul_smul σ τ v

example (σ : F ≃ₐ[K] F) (v : Place K F) (f : F) : (σ • v).ord (σ f) = v.ord f :=
  Place.ord_smul σ v f

example (σ : F ≃ₐ[K] F) (v : Place K F) : (σ • v).deg = v.deg := Place.deg_smul σ v

/-- A finite residue extension stays finite along `σ`, through `Place.smulResidueAlgEquiv`. -/
example (σ : F ≃ₐ[K] F) (v : Place K F) [Module.Finite K v.ResidueField] :
    Module.Finite K (σ • v).ResidueField :=
  Module.Finite.equiv (Place.smulResidueAlgEquiv σ v).toLinearEquiv

/-! The action on divisors. -/

example (σ : F ≃ₐ[K] F) (D : Divisor K F) : σ • D = Finsupp.mapDomain (σ • ·) D := rfl

example (σ : F ≃ₐ[K] F) (D : Divisor K F) (w : Place K F) : (σ • D) w = D (σ⁻¹ • w) :=
  Divisor.smul_apply σ D w

example (σ : F ≃ₐ[K] F) (v : Place K F) (n : ℤ) :
    σ • Finsupp.single v n = Finsupp.single (σ • v) n := by
  simp

example (σ : F ≃ₐ[K] F) (D : Divisor K F) : σ⁻¹ • σ • D = D := inv_smul_smul σ D

example (σ : F ≃ₐ[K] F) (D : Divisor K F) : Divisor.degree (σ • D) = Divisor.degree D := by
  simp

example (σ : F ≃ₐ[K] F) {D : Divisor K F} (hD : D ∈ Divisor.principal (K := K) (F := F)) :
    σ • D ∈ Divisor.principal (K := K) (F := F) :=
  Divisor.smul_mem_principal σ hD

/-! The action on `Pic0`. -/

example (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    (Pic0.degZeroSMulHom σ D : Divisor K F) = σ • (D : Divisor K F) :=
  rfl

example (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    σ • Pic0.mk D = Pic0.mk (Pic0.degZeroSMulHom σ D) :=
  rfl

example (σ τ : F ≃ₐ[K] F) (c : Pic0 K F) : (σ * τ) • c = σ • τ • c := mul_smul σ τ c

example (σ : F ≃ₐ[K] F) (c d : Pic0 K F) : σ • (c + d) = σ • c + σ • d := smul_add σ c d

example (σ : F ≃ₐ[K] F) (c : Pic0 K F) : σ⁻¹ • σ • c = c := inv_smul_smul σ c

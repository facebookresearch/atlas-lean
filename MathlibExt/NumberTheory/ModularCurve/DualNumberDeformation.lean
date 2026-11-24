/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_algHom_dualNumber_
  fst_eq_snd_ne_zero_rigidDataH1Pow.lean`
and
`P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_algHom_dualNumber_
  fst_eq_snd_ne_zero_rigidDataH1Pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.DualNumber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic

@[expose] public section

namespace Algebra

variable {A B Ω : Type*} [CommRing A] [CommRing B] [Field Ω]
  [Algebra A B] [Algebra A Ω]

/-- A nonzero derivation of an algebra into a field, relative to a
chosen point of the algebra in that field, gives a lift of the point
to the dual numbers whose tangent component is nonzero somewhere.
This is the tangent-space step behind first-order deformations of a
moduli point: the lift is `b ↦ (φ₀ b, D b)`. -/
theorem exists_algHom_dualNumber_fst_eq_snd_ne_zero
    (φ₀ : B →ₐ[A] Ω) (D : B → Ω)
    (hDadd : ∀ x y : B, D (x + y) = D x + D y)
    (hDmul : ∀ x y : B, D (x * y) = φ₀ x * D y + D x * φ₀ y)
    (hDA : ∀ (a : A) (x : B), D (algebraMap A B a * x) = algebraMap A Ω a * D x)
    (hD : ∃ b : B, D b ≠ 0) :
    ∃ φ : B →ₐ[A] DualNumber Ω,
      (∀ b : B, (φ b).fst = φ₀ b) ∧ ∃ b : B, (φ b).snd ≠ 0 := by
  have hD1 : D 1 = 0 := by
    have h := hDmul 1 1
    simp only [map_one, mul_one, one_mul] at h
    simpa using h.symm
  have hD0 : D 0 = 0 := by
    have h := hDadd 0 0
    simp only [add_zero] at h
    simpa using h.symm
  refine ⟨{
    toFun := fun b => (φ₀ b, D b)
    map_one' := by
      apply TrivSqZeroExt.ext
      · simp
      · simp [hD1]
    map_mul' := fun x y => by
      apply TrivSqZeroExt.ext
      · exact map_mul φ₀ x y
      · exact hDmul x y
    map_zero' := by
      apply TrivSqZeroExt.ext
      · simp
      · simp [hD0]
    map_add' := fun x y => by
      apply TrivSqZeroExt.ext
      · exact map_add φ₀ x y
      · exact hDadd x y
    commutes' := fun a => by
      apply TrivSqZeroExt.ext
      · simp [TrivSqZeroExt.algebraMap_eq_inl', φ₀.commutes a]
      · have h := hDA a 1
        rw [mul_one, hD1, mul_zero] at h
        simp [TrivSqZeroExt.algebraMap_eq_inl', h] }, fun b => rfl, ?_⟩
  obtain ⟨b, hb⟩ := hD
  exact ⟨b, hb⟩

end Algebra

namespace ModularCurve.FullLevel.Diamond

open Algebra

variable {A B Ω : Type*} [CommRing A] [CommRing B] [Field Ω]
  [Algebra A B] [Algebra A Ω]

/-- A rigidified full-level moduli point over an algebraically closed
field of characteristic zero, at a prime level prime to the auxiliary
level and at a prime `ℓg ≡ 11 [MOD 12]` dividing the auxiliary level,
admits a nontrivial first-order deformation: given the nonzero
tangent derivation supplied by the rigidified level data, the point
lifts to the dual numbers, agreeing with the original point in the
first component and with nonzero tangent component somewhere. -/
theorem exists_algHom_dualNumber_fst_eq_snd_ne_zero_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : Nat.Prime ℓg) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    [IsAlgClosed Ω] [CharZero Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (φ₀ : B →ₐ[A] Ω) (D : B → Ω)
    (hDadd : ∀ x y : B, D (x + y) = D x + D y)
    (hDmul : ∀ x y : B, D (x * y) = φ₀ x * D y + D x * φ₀ y)
    (hDA : ∀ (a : A) (x : B), D (algebraMap A B a * x) = algebraMap A Ω a * D x)
    (hD : ∃ b : B, D b ≠ 0) :
    ∃ φ : B →ₐ[A] DualNumber Ω,
      (∀ b : B, (φ b).fst = φ₀ b) ∧ ∃ b : B, (φ b).snd ≠ 0 :=
  Algebra.exists_algHom_dualNumber_fst_eq_snd_ne_zero φ₀ D hDadd hDmul hDA hD

end ModularCurve.FullLevel.Diamond

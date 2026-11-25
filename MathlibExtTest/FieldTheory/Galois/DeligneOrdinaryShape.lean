/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.DeligneOrdinaryShape

@[expose] public section

namespace GaloisRepDeligneOrdinaryShapeTest

/-- Consumer with the original shape binders. -/
public theorem exactSource {A : Type*} [CommRing A] {H : Type*} [Group H]
    (ρloc : H →* Matrix.GeneralLinearGroup (Fin 2) A) (I : Subgroup H)
    (frob : H) (χ : H →* A) (k : ℕ) (ap εp : A)
    (h : GaloisRep.DeligneOrdinaryShape ρloc I frob χ k ap εp) :
    (h.conj * ρloc frob * h.conj⁻¹).val 1 1 = ap :=
  h.conj_frob_apply_one_one

/-- Higher-universe consumer: one conjugating element makes every group
element upper-triangular. -/
public theorem exactSourceTypeOne {A : Type 1} [CommRing A] {H : Type 1}
    [Group H] (ρloc : H →* Matrix.GeneralLinearGroup (Fin 2) A)
    (I : Subgroup H) (frob : H) (χ : H →* A) (k : ℕ) (ap εp : A)
    (h : GaloisRep.DeligneOrdinaryShape ρloc I frob χ k ap εp) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) A,
      ∀ σ : H, (g * ρloc σ * g⁻¹).val 1 0 = 0 :=
  ⟨h.conj, h.conj_apply_one_zero⟩

/-- The trivial representation satisfies the shape. -/
public example {A : Type*} [CommRing A] {H : Type*} [Group H]
    (I : Subgroup H) (frob : H) (k : ℕ) :
    GaloisRep.DeligneOrdinaryShape (1 : H →* Matrix.GeneralLinearGroup
      (Fin 2) A) I frob 1 k 1 1 :=
  GaloisRep.deligneOrdinaryShape_one I frob k

/-- Inertia acts through `χ ^ (k - 1)` on the upper-left entry and trivially
on the lower-right entry of the same upper-triangular conjugate, so an
inertia element has determinant `χ σ ^ (k - 1)`. -/
public example {A : Type*} [CommRing A] {H : Type*} [Group H]
    (ρloc : H →* Matrix.GeneralLinearGroup (Fin 2) A) (I : Subgroup H)
    (frob : H) (χ : H →* A) (k : ℕ) (ap εp : A)
    (h : GaloisRep.DeligneOrdinaryShape ρloc I frob χ k ap εp) {σ : H}
    (hσ : σ ∈ I) :
    (ρloc σ).val.det = χ σ ^ (k - 1) := by
  rw [← Matrix.det_units_conj h.conj (ρloc σ).val, ← Units.val_mul,
    ← Units.val_mul, Matrix.det_fin_two, h.conj_apply_one_zero,
    h.conj_inertia_apply_one_one hσ, h.conj_inertia_apply_zero_zero hσ]
  ring

/-- The Frobenius clauses hold for the same upper-triangular conjugate, so
Frobenius has determinant `χ(frob) ^ (k - 1) * εp`. -/
public example {A : Type*} [CommRing A] {H : Type*} [Group H]
    (ρloc : H →* Matrix.GeneralLinearGroup (Fin 2) A) (I : Subgroup H)
    (frob : H) (χ : H →* A) (k : ℕ) (ap εp : A)
    (h : GaloisRep.DeligneOrdinaryShape ρloc I frob χ k ap εp) :
    (ρloc frob).val.det = χ frob ^ (k - 1) * εp := by
  rw [← Matrix.det_units_conj h.conj (ρloc frob).val, ← Units.val_mul,
    ← Units.val_mul, Matrix.det_fin_two, h.conj_apply_one_zero,
    h.conj_frob_apply_one_one, ← h.conj_frob_mul_apply_zero_zero]
  ring

end GaloisRepDeligneOrdinaryShapeTest

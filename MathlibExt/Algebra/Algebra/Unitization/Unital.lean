/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Tactic.Abel

/-!
# Unitization of an already unital algebra

For a unital algebra `A`, its forced unitization is algebra-equivalent to the
product of the scalars and `A`. The equivalence is the shear

`(r, a) ↦ (r, r • 1 + a)`

with inverse `(r, b) ↦ (r, b - r • 1)`.

This algebraic equivalence is the common lower-layer core of the existing
normed continuous and C-star star-algebra unitization equivalences. This module
contains no K-theory-specific data.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Unitization

noncomputable section

universe u v

/-- Let `R` be a commutative ring and `A` a unital `R`-algebra. The map from the unitization to `R × A`
sends `(r,a)` to `(r, r • 1 + a)` and is an `R`-algebra homomorphism.
-/
def unitalProdAlgHom
    (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A] :
    Unitization R A →ₐ[R] R × A :=
  (fstHom R A).prod (lift (NonUnitalAlgHom.id R A))

/-- Let `R` be a commutative ring and `A` a unital `R`-algebra. For `x` in the unitization, the
homomorphism has value `(x.fst, x.fst • 1 + x.snd)`.
-/
theorem unitalProdAlgHom_apply
    (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A]
    (x : Unitization R A) :
    unitalProdAlgHom R A x = (x.fst, x.fst • (1 : A) + x.snd) := by
  apply Prod.ext
  · rfl
  · change algebraMap R A x.fst + x.snd = x.fst • (1 : A) + x.snd
    rw [Algebra.algebraMap_eq_smul_one]

/-- Let `R` be a commutative ring and `A` a unital `R`-algebra. The shear map `(r,a) ↦ (r, r • 1 + a)`
gives an `R`-algebra equivalence from the unitization of `A` to `R × A`.
-/
def unitalProdAlgEquiv
    (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A] :
    Unitization R A ≃ₐ[R] R × A :=
  AlgEquiv.ofBijective (unitalProdAlgHom R A) (by
    constructor
    · intro x y hxy
      have hfst : x.fst = y.fst := by
        simpa only [unitalProdAlgHom_apply] using congrArg Prod.fst hxy
      have hsnd : x.snd = y.snd := by
        have h := congrArg Prod.snd hxy
        simp only [unitalProdAlgHom_apply] at h
        rw [hfst] at h
        exact add_left_cancel h
      exact Unitization.ext hfst hsnd
    · rintro ⟨c, b⟩
      let y : Unitization R A := inl c +
        inr (R := R) (A := A) (b - c • (1 : A))
      refine ⟨y, ?_⟩
      rw [unitalProdAlgHom_apply]
      apply Prod.ext
      · simp only [y, fst_add, fst_inl, fst_inr, add_zero]
      · simp only [y, fst_add, fst_inl, fst_inr, add_zero, snd_add,
          snd_inl, snd_inr, zero_add]
        abel)

/-- Let `R` be a commutative ring and `A` a unital `R`-algebra. The unitization/product equivalence
sends `x` to `(x.fst, x.fst • 1 + x.snd)`.
-/
@[simp]
theorem unitalProdAlgEquiv_apply
    (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A]
    (x : Unitization R A) :
    unitalProdAlgEquiv R A x = (x.fst, x.fst • (1 : A) + x.snd) :=
  unitalProdAlgHom_apply R A x

/-- Let `R` be a commutative ring and `A` a unital `R`-algebra. The first coordinate of the image of a
unitization element `x` is its scalar coordinate `x.fst`.
-/
theorem unitalProdAlgEquiv_apply_fst
    (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A]
    (x : Unitization R A) :
    (unitalProdAlgEquiv R A x).1 = x.fst := by
  rw [unitalProdAlgEquiv_apply]

/-- Let `R` be a commutative ring and `A` a unital `R`-algebra. The second coordinate of the image of
`x` is `x.fst • 1 + x.snd`.
-/
theorem unitalProdAlgEquiv_apply_snd
    (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A]
    (x : Unitization R A) :
    (unitalProdAlgEquiv R A x).2 = x.fst • (1 : A) + x.snd := by
  rw [unitalProdAlgEquiv_apply]

/-- Let `R` be a commutative ring and `A` a unital `R`-algebra. The inverse equivalence sends `(r,a)` to
`inl r + inr (a - r • 1)`.
-/
@[simp]
theorem unitalProdAlgEquiv_symm_apply
    (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A]
    (x : R × A) :
    (unitalProdAlgEquiv R A).symm x =
      inl x.1 + inr (R := R) (A := A) (x.2 - x.1 • (1 : A)) := by
  let y : Unitization R A := inl x.1 +
    inr (R := R) (A := A) (x.2 - x.1 • (1 : A))
  apply (unitalProdAlgEquiv R A).injective
  calc
    unitalProdAlgEquiv R A ((unitalProdAlgEquiv R A).symm x) = x :=
      (unitalProdAlgEquiv R A).apply_symm_apply x
    _ = unitalProdAlgEquiv R A y := by
      rw [unitalProdAlgEquiv_apply]
      apply Prod.ext
      · simp only [y, fst_add, fst_inl, fst_inr, add_zero]
      · simp only [y, fst_add, fst_inl, fst_inr, add_zero, snd_add,
          snd_inl, snd_inr, zero_add]
        abel

/-- Let `R` be a commutative ring and `A` a unital `R`-algebra. The scalar inclusion of `r` has image
`(r, r • 1)` under the unitization/product equivalence.
-/
theorem unitalProdAlgEquiv_inl
    (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A] (r : R) :
    unitalProdAlgEquiv R A (inl r) = (r, r • (1 : A)) := by
  rw [unitalProdAlgEquiv_apply]
  simp only [fst_inl, snd_inl, add_zero]

/-- Let `R` be a commutative ring and `A` a unital `R`-algebra. The ideal inclusion of `a` has image
`(0,a)` under the unitization/product equivalence.
-/
theorem unitalProdAlgEquiv_inr
    (R : Type u) (A : Type v)
    [CommRing R] [Ring A] [Algebra R A] (a : A) :
    unitalProdAlgEquiv R A (inr a) = (0, a) := by
  rw [unitalProdAlgEquiv_apply]
  simp only [fst_inr, zero_smul, snd_inr, zero_add]

end

end Unitization

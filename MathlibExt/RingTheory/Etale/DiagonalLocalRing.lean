/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RingTheory.Localization.AtPrimeFlatQuotient
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The actual local diagonal of an étale algebra

For an étale algebra, tensor multiplication is itself étale, hence flat.
Its canonical localization at a prime on the diagonal is an isomorphism.
The original tensor product, multiplication map, and inverse-image prime
are retained. No diagonal regularity or resolution is supplied as a premise.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace Algebra.TensorProduct

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The tensor multiplication map is surjective by its literal left section. -/
theorem lmul'_surjective :
    Function.Surjective (lmul' (S := A) R) := by
  intro a
  exact ⟨a ⊗ₜ[R] 1, by simp⟩

/-- The actual multiplication map of an étale algebra is flat. -/
theorem lmul'_flat [Algebra.Etale R A] :
    (lmul' (S := A) R).toRingHom.Flat := by
  let : Algebra (A ⊗[R] A) A := (lmul' (S := A) R).toRingHom.toAlgebra
  let : IsScalarTower A (A ⊗[R] A) A :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change a = lmul' R (a ⊗ₜ[R] 1)
      simp)
  let : Algebra.Etale (A ⊗[R] A) A :=
    Algebra.Etale.of_restrictScalars A (A ⊗[R] A) A
  exact inferInstanceAs (Module.Flat (A ⊗[R] A) A)

/-- The original canonical local map at a prime of the étale diagonal is
bijective, even when the étale algebra has several components. -/
theorem localRingHom_lmul'_bijective [Algebra.Etale R A]
    (p : Ideal A) [p.IsPrime] :
    Function.Bijective
      (Localization.localRingHom
        (p.comap (lmul' (S := A) R).toRingHom) p
        (lmul' (S := A) R).toRingHom rfl) :=
  Localization.localRingHom_bijective_of_flat_of_surjective
    (lmul' (S := A) R).toRingHom lmul'_surjective lmul'_flat p

/-- The local ring isomorphism uses the actual diagonal multiplication map
as its forward map. -/
def etaleDiagonalLocalRingEquiv [Algebra.Etale R A]
    (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime (p.comap (lmul' (S := A) R).toRingHom) ≃+*
      Localization.AtPrime p :=
  RingEquiv.ofBijective
    (Localization.localRingHom
      (p.comap (lmul' (S := A) R).toRingHom) p
      (lmul' (S := A) R).toRingHom rfl)
    (localRingHom_lmul'_bijective p)

/-- The comparison evaluates to the original canonical local ring map. -/
theorem etaleDiagonalLocalRingEquiv_apply [Algebra.Etale R A]
    (p : Ideal A) [p.IsPrime]
    (x : Localization.AtPrime (p.comap (lmul' (S := A) R).toRingHom)) :
    etaleDiagonalLocalRingEquiv p x =
      Localization.localRingHom
        (p.comap (lmul' (S := A) R).toRingHom) p
        (lmul' (S := A) R).toRingHom rfl x := rfl

end Algebra.TensorProduct

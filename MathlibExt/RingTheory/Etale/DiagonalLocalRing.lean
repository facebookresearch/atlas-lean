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
# Local ring comparison along an étale diagonal

Let A be a commutative R-algebra, with independent ring universes. Tensor multiplication μ:A⊗_R
A→A is surjective through a↦a⊗1. If A is étale over R, μ is flat.

For a prime p of A and q=μ⁻¹(p), the canonical local ring map (A⊗_R A)_q→A_p is therefore
bijective and gives a ring isomorphism. The isomorphism uses that local map as its forward
morphism, with no connectedness or single-component assumption on A.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace Algebra.TensorProduct

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Let R,A be commutative rings in independent universes u,v, with A an R-algebra. Write μ:A⊗_R A→A
for tensor multiplication. The map μ is surjective because μ(a⊗1)=a for every a∈A. This
statement requires no étaleness assumption. -/
theorem lmul'_surjective :
    Function.Surjective (lmul' (S := A) R) := by
  intro a
  exact ⟨a ⊗ₜ[R] 1, by simp⟩

/-- Let R,A be commutative rings in independent universes u,v, with A an R-algebra. Write μ:A⊗_R A→A
for tensor multiplication. If A is étale over R, μ is a flat ring homomorphism. The induced
algebra structure on A over A⊗_R A is étale, so its underlying module is flat. -/
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

/-- Let R,A be commutative rings in independent universes u,v, with A an R-algebra. Write μ:A⊗_R A→A
for tensor multiplication. Assume A is étale over R and p⊂A is prime. With q=μ⁻¹(p), the
canonical map (A⊗_R A)_q→A_p induced by μ is bijective. Tensor multiplication is flat and
surjective, so its target-prime local map is an isomorphism. -/
theorem localRingHom_lmul'_bijective [Algebra.Etale R A]
    (p : Ideal A) [p.IsPrime] :
    Function.Bijective
      (Localization.localRingHom
        (p.comap (lmul' (S := A) R).toRingHom) p
        (lmul' (S := A) R).toRingHom rfl) :=
  Localization.localRingHom_bijective_of_flat_of_surjective
    (lmul' (S := A) R).toRingHom lmul'_surjective lmul'_flat p

/-- Let R,A be commutative rings in independent universes u,v, with A an R-algebra. Write μ:A⊗_R A→A
for tensor multiplication. For A étale over R and prime p⊂A, this is the ring isomorphism (A⊗_R
A)_{μ⁻¹(p)}≅A_p induced by the canonical local map of tensor multiplication. -/
def etaleDiagonalLocalRingEquiv [Algebra.Etale R A]
    (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime (p.comap (lmul' (S := A) R).toRingHom) ≃+*
      Localization.AtPrime p :=
  RingEquiv.ofBijective
    (Localization.localRingHom
      (p.comap (lmul' (S := A) R).toRingHom) p
      (lmul' (S := A) R).toRingHom rfl)
    (localRingHom_lmul'_bijective p)

/-- Let R,A be commutative rings in independent universes u,v, with A an R-algebra. Write μ:A⊗_R A→A
for tensor multiplication. Assume A is étale over R and p is prime. The forward value of the
diagonal ring isomorphism on x∈(A⊗_R A)_{μ⁻¹(p)} equals the canonical local-ring homomorphism
induced by μ, evaluated at x. -/
theorem etaleDiagonalLocalRingEquiv_apply [Algebra.Etale R A]
    (p : Ideal A) [p.IsPrime]
    (x : Localization.AtPrime (p.comap (lmul' (S := A) R).toRingHom)) :
    etaleDiagonalLocalRingEquiv p x =
      Localization.localRingHom
        (p.comap (lmul' (S := A) R).toRingHom) p
        (lmul' (S := A) R).toRingHom rfl x := rfl

end Algebra.TensorProduct

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

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Group.Commute.Defs

/-!
# Compression by a star projection commuting with a represented algebra

For a possibly nonunital involutive algebra homomorphism, multiplication by a
self-adjoint idempotent commuting with its image defines another homomorphism.
The construction is algebraic: it assumes no norm, topology or completeness.
Its action is the usual two-sided compression, but the one-sided formula
avoids duplicating associativity and idempotence work in each defining law.
-/

@[expose] public section

namespace NonUnitalStarAlgHom

universe uR uA uD uC

variable {R : Type uR} {A : Type uA} {D : Type uD} {C : Type uC}
variable [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalSemiring D] [DistribMulAction R D] [StarRing D]
variable [SMulCommClass R D D]

/-- Let `R` be a monoid acting additively on a possibly nonunital, nonassociative semiring `A` with a
star operation and on a possibly nonunital star semiring `D`. Assume the `R`-action on `D` commutes
with left multiplication. Let `rho : A →⋆ₙₐ[R] D` and let `p` be a star projection commuting with
every `rho a`. Projection compression defines another nonunital star homomorphism; its value is `p *
rho a`.
-/
def compress (rho : A →⋆ₙₐ[R] D) (p : D) (hp : IsStarProjection p)
    (hcomm : ∀ a : A, Commute p (rho a)) : A →⋆ₙₐ[R] D where
  toFun := fun a ↦ p * rho a
  map_zero' := by rw [map_zero, mul_zero]
  map_add' a b := by rw [map_add, mul_add]
  map_smul' r a := by
    change p * rho (r • a) = r • (p * rho a)
    rw [map_smul, mul_smul_comm]
  map_mul' a b := by
    rw [map_mul]
    calc
      p * (rho a * rho b) = p * p * (rho a * rho b) := by
        rw [hp.isIdempotentElem.eq]
      _ = (p * rho a) * (p * rho b) :=
        ((hcomm a).symm.mul_mul_mul_comm p (rho b)).symm
  map_star' a := by
    rw [map_star, star_mul, hp.isSelfAdjoint.star_eq]
    simpa only [map_star] using (hcomm (star a)).eq

/-- Let `R` be a monoid acting additively on a possibly nonunital, nonassociative semiring `A` with a
star operation and on a possibly nonunital star semiring `D`. Assume the `R`-action on `D` commutes
with left multiplication. Let `rho : A →⋆ₙₐ[R] D` and let `p` be a star projection commuting with
every `rho a`. At `a ∈ A`, the compressed homomorphism has value `p * rho a`.
-/
@[simp]
theorem compress_apply (rho : A →⋆ₙₐ[R] D) (p : D)
    (hp : IsStarProjection p) (hcomm : ∀ a : A, Commute p (rho a)) (a : A) :
    compress rho p hp hcomm a = p * rho a :=
  rfl

/-- Let `R` be a monoid acting additively on a possibly nonunital, nonassociative semiring `A` with a
star operation and on a possibly nonunital star semiring `D`. Assume the `R`-action on `D` commutes
with left multiplication. Let `rho : A →⋆ₙₐ[R] D` and let `p` be a star projection commuting with
every `rho a`. The one-sided formula also equals `p * rho a * p`, so this is two-sided projection
compression.
-/
theorem compress_apply_eq_mul_mul (rho : A →⋆ₙₐ[R] D) (p : D)
    (hp : IsStarProjection p) (hcomm : ∀ a : A, Commute p (rho a)) (a : A) :
    compress rho p hp hcomm a = p * rho a * p := by
  rw [compress_apply, mul_assoc, ← (hcomm a).eq, ← mul_assoc,
    hp.isIdempotentElem.eq]

/-- Let `R` act additively on a possibly nonunital, nonassociative semiring `A` with star and on a
possibly nonunital star semiring `D`, with the action on `D` commuting with left multiplication. For
`rho : A →⋆ₙₐ[R] D`, compression at the zero projection is zero at every `a ∈ A`.
-/
theorem compress_zero_apply (rho : A →⋆ₙₐ[R] D) (a : A) :
    compress rho 0 (IsStarProjection.zero D)
      (fun a ↦ by exact (zero_mul (rho a)).trans (mul_zero (rho a)).symm) a =
      0 :=
  zero_mul (rho a)

/-- Let `R` be a monoid acting additively on a possibly nonunital, nonassociative semiring `A` with a
star operation and on a possibly nonunital star semiring `D`. Assume the `R`-action on `D` commutes
with left multiplication. Let `rho : A →⋆ₙₐ[R] D` and let `p` be a star projection commuting with
every `rho a`. For another nonunital semiring `C` with additive `R`-action and star, and a
homomorphism `f : C →⋆ₙₐ[R] A`, compressing `rho ∘ f` agrees with precomposing the compression of
`rho` by `f`.
-/
theorem compress_comp
    [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]
    (rho : A →⋆ₙₐ[R] D) (p : D) (hp : IsStarProjection p)
    (hcomm : ∀ a : A, Commute p (rho a)) (f : C →⋆ₙₐ[R] A) :
    compress (rho.comp f) p hp (fun c ↦ hcomm (f c)) =
      (compress rho p hp hcomm).comp f := by
  ext c
  rfl

section UnitalCodomain

variable {U : Type uD} [Semiring U] [DistribMulAction R U] [StarRing U]
variable [SMulCommClass R U U]

/-- Let `R` act additively on a possibly nonunital, nonassociative semiring `A` with star and on a
unital star semiring `U`, with the action on `U` commuting with left multiplication. Compression of
`rho : A →⋆ₙₐ[R] U` at the identity is `rho` itself.
-/
@[simp]
theorem compress_one (rho : A →⋆ₙₐ[R] U) :
    compress rho 1 (IsStarProjection.one U)
      (fun a ↦ by exact (one_mul (rho a)).trans (mul_one (rho a)).symm) =
      rho := by
  ext a
  exact one_mul (rho a)

end UnitalCodomain

end NonUnitalStarAlgHom

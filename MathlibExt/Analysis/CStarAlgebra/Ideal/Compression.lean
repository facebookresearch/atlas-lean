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

public import MathlibExt.Algebra.Star.Compression
public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient

/-!
# Projection compression modulo a closed star ideal

An essentially self-adjoint idempotent commuting with a represented algebra
modulo an ideal gives an actual star-algebra homomorphism into the quotient.
The representation's source algebra is algebraic and possibly nonunital.
Exact ambient projections are a special case, not a restriction of the
essentially-projection carrier used in Fredholm and extension constructions.
-/

@[expose] public section

noncomputable section

open scoped NonUnitalStarSubalgebra.Quotient

namespace ClosedStarIdeal

universe uA uD

variable {A : Type uA} {D : Type uD}
variable [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [Star A]
variable [NonUnitalCStarAlgebra D]

/-- **Projection compression modulo an ideal.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and a star operation, let `D` be a nonunital complex
C*-algebra, and let `I ⊆ D` be a closed two-sided star ideal. A compression pair consists of a
complex nonunital star homomorphism `ρ : A → D` and `p ∈ D` such that `p²-p`, `p*-p`, and every
commutator `pρ(a)-ρ(a)p` belong to `I`. -/
structure CompressionPair (A : Type uA) (D : Type uD)
    [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [Star A]
    [NonUnitalCStarAlgebra D] (I : ClosedStarIdeal D) where
  /-- The possibly nonunital source representation. -/
  representation : A →⋆ₙₐ[ℂ] D
  /-- The ambient element whose class is a projection. -/
  projection : D
  /-- Its square defect belongs to the ideal. -/
  square_mem : projection * projection - projection ∈ I
  /-- Its adjoint defect belongs to the ideal. -/
  adjoint_mem : star projection - projection ∈ I
  /-- It commutes with the representation modulo the ideal. -/
  commutator_mem : ∀ a : A,
    projection * representation a - representation a * projection ∈ I

namespace CompressionPair

variable {I : ClosedStarIdeal D}

/-- **Compressed projection class.** Let `A` be a nonunital, possibly nonassociative semiring with a
distributive complex scalar action and a star operation, let `D` be a nonunital complex C*-algebra,
and let `I ⊆ D` be a closed two-sided star ideal. For a compression pair `(ρ,p)`, the class of `p`
in `D/I` is self-adjoint and idempotent. -/
theorem quotient_isStarProjection (P : CompressionPair A D I) :
    let _ : I.carrier.IsTwoSided := I.isTwoSided
    IsStarProjection (I.quotientMap P.projection) := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  apply isStarProjection_iff'.2
  constructor
  · have h := (I.quotientMap_eq_zero_iff
      (P.projection * P.projection - P.projection)).2 P.square_mem
    rw [map_sub, map_mul, sub_eq_zero] at h
    exact h
  · have h := (I.quotientMap_eq_zero_iff
      (star P.projection - P.projection)).2 P.adjoint_mem
    rw [map_sub, map_star, sub_eq_zero] at h
    exact h

/-- **Compression commutes modulo the ideal.** Let `A` be a nonunital, possibly nonassociative semiring
with a distributive complex scalar action and a star operation, let `D` be a nonunital complex
C*-algebra, and let `I ⊆ D` be a closed two-sided star ideal. For a compression pair `(ρ,p)` and
every `a ∈ A`, the class of `p` in `D/I` commutes with the class of `ρ(a)`. -/
theorem quotient_commute (P : CompressionPair A D I) (a : A) :
    let _ : I.carrier.IsTwoSided := I.isTwoSided
    Commute (I.quotientMap P.projection)
      ((I.quotientMap.comp P.representation) a) := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  have h := (I.quotientMap_eq_zero_iff
    (P.projection * P.representation a -
      P.representation a * P.projection)).2 (P.commutator_mem a)
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

/-- **Compressed quotient homomorphism.** Let `A` be a nonunital, possibly nonassociative semiring with
a distributive complex scalar action and a star operation, let `D` be a nonunital complex
C*-algebra, and let `I ⊆ D` be a closed two-sided star ideal. A compression pair `(ρ,p)` defines the
complex nonunital star homomorphism `A → D/I` sending `a` to the class of `pρ(a)p`. -/
def quotientHom (P : CompressionPair A D I) :
    let _ : I.carrier.IsTwoSided := I.isTwoSided
    A →⋆ₙₐ[ℂ] I.Quotient := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  exact NonUnitalStarAlgHom.compress
    (I.quotientMap.comp P.representation)
    (I.quotientMap P.projection)
    P.quotient_isStarProjection P.quotient_commute

/-- **Evaluation of the compressed quotient map.** Let `A` be a nonunital, possibly nonassociative
semiring with a distributive complex scalar action and a star operation, let `D` be a nonunital
complex C*-algebra, and let `I ⊆ D` be a closed two-sided star ideal. For a compression pair `(ρ,p)`
and every `a ∈ A`, the compressed quotient homomorphism evaluates to `[pρ(a)p]` in `D/I`. -/
theorem quotientHom_apply (P : CompressionPair A D I) (a : A) :
    let _ : I.carrier.IsTwoSided := I.isTwoSided
    P.quotientHom a =
      I.quotientMap (P.projection * P.representation a * P.projection) := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  rw [quotientHom, NonUnitalStarAlgHom.compress_apply_eq_mul_mul]
  rw [map_mul, map_mul]
  rfl

/-- **Compression pair from an exact projection.** Let `A` be a nonunital, possibly nonassociative
semiring with a distributive complex scalar action and a star operation, let `D` be a nonunital
complex C*-algebra, and let `I ⊆ D` be a closed two-sided star ideal. If `ρ : A → D` is a complex
nonunital star homomorphism, `p` is a self-adjoint idempotent, and `pρ(a)-ρ(a)p ∈ I` for every `a`,
then `(ρ,p)` is a compression pair modulo `I`. -/
def ofProjection (I : ClosedStarIdeal D) (rho : A →⋆ₙₐ[ℂ] D) (p : D)
    (hp : IsStarProjection p)
    (hcomm : ∀ a : A, p * rho a - rho a * p ∈ I) :
    CompressionPair A D I where
  representation := rho
  projection := p
  square_mem := by
    rw [hp.isIdempotentElem.eq, sub_self]
    exact I.carrier.zero_mem
  adjoint_mem := by
    rw [hp.isSelfAdjoint.star_eq, sub_self]
    exact I.carrier.zero_mem
  commutator_mem := hcomm

/-- **Representation of an exact-projection compression pair.** Let `A` be a nonunital, possibly
nonassociative semiring with a distributive complex scalar action and a star operation, let `D` be a
nonunital complex C*-algebra, and let `I ⊆ D` be a closed two-sided star ideal. The pair constructed
from a self-adjoint idempotent `p` commuting with `ρ(A)` modulo `I` has representation `ρ`. -/
@[simp]
theorem ofProjection_representation (I : ClosedStarIdeal D)
    (rho : A →⋆ₙₐ[ℂ] D) (p : D) (hp : IsStarProjection p)
    (hcomm : ∀ a : A, p * rho a - rho a * p ∈ I) :
    (ofProjection I rho p hp hcomm).representation = rho :=
  rfl

/-- **Projection of an exact-projection compression pair.** Let `A` be a nonunital, possibly
nonassociative semiring with a distributive complex scalar action and a star operation, let `D` be a
nonunital complex C*-algebra, and let `I ⊆ D` be a closed two-sided star ideal. The pair constructed
from a self-adjoint idempotent `p` commuting with `ρ(A)` modulo `I` has projection element `p`. -/
@[simp]
theorem ofProjection_projection (I : ClosedStarIdeal D)
    (rho : A →⋆ₙₐ[ℂ] D) (p : D) (hp : IsStarProjection p)
    (hcomm : ∀ a : A, p * rho a - rho a * p ∈ I) :
    (ofProjection I rho p hp hcomm).projection = p :=
  rfl

end CompressionPair
end ClosedStarIdeal

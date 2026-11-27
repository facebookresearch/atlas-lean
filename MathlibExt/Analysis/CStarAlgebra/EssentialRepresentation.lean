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

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The actual essential Hilbert subspace of a nonunital representation

Take the closure of the span of all original operator values. Every operator
has its range in this closed subspace, so its restriction is literal domain
and codomain restriction of the original bounded linear map. The original
adjoint identity gives the restricted star-algebra representation.

The basic closed span and restriction require only the algebraic nonunital
star-homomorphism carrier, with no topology or C-star structure on the source.
The restriction has the same zero kernel and is nondegenerate on this actual
essential subspace. Injectivity uses only the source additive group; the
norm statement retains the original source C-star hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace NonUnitalStarAlgHom

universe uA uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Algebraic

variable {A : Type uA} [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [Star A]

/-- **Essential subspace of a representation.** Let `H` be a complete complex Hilbert space and let `A`
be a nonunital, possibly nonassociative semiring with a distributive complex scalar action and a
star operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars, and star. The
essential subspace is the norm-closed complex-linear span of all vectors `ρ(a)ξ`, for `a ∈ A` and `ξ
∈ H`. -/
def essentialSpace (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range fun p : A × H => ρ p.1 p.2)).topologicalClosure

/-- The essential subspace has its ordinary closed-subspace Hilbert completeness. -/
instance completeSpaceEssentialSpace (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    CompleteSpace ↥ρ.essentialSpace :=
  (Submodule.span ℂ (Set.range fun p : A × H => ρ p.1 p.2)).isClosed_topologicalClosure.completeSpace_coe

/-- **Representation values lie in the essential subspace.** Let `H` be a complete complex Hilbert space
and let `A` be a nonunital, possibly nonassociative semiring with a distributive complex scalar
action and a star operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars,
and star. For every `a ∈ A` and `ξ ∈ H`, `ρ(a)ξ` belongs to the essential subspace. -/
theorem range_mem_essentialSpace (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) (ξ : H) :
    ρ a ξ ∈ ρ.essentialSpace :=
  (Submodule.span ℂ (Set.range fun p : A × H => ρ p.1 p.2)).le_topologicalClosure
    (Submodule.subset_span ⟨(a, ξ), rfl⟩)

/-- **Operator restricted to the essential subspace.** Let `H` be a complete complex Hilbert space and
let `A` be a nonunital, possibly nonassociative semiring with a distributive complex scalar action
and a star operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars, and
star. For `a ∈ A`, the operator `ρ(a)` restricts to a bounded operator on the closed essential
subspace of `ρ`, with the inherited Hilbert norm. -/
def essentialOperator (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    ρ.essentialSpace →L[ℂ] ρ.essentialSpace :=
  ((ρ a).domRestrict ρ.essentialSpace).codRestrict ρ.essentialSpace
    fun ξ => ρ.range_mem_essentialSpace a ξ

/-- **Values of the essential operator.** Let `H` be a complete complex Hilbert space and let `A` be a
nonunital, possibly nonassociative semiring with a distributive complex scalar action and a star
operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars, and star. For `a ∈
A` and `ξ` in the essential subspace, including the restricted operator value into `H` gives
`ρ(a)ξ`. -/
@[simp]
theorem essentialOperator_apply_coe (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A)
    (ξ : ρ.essentialSpace) :
    (ρ.essentialOperator a ξ : H) = ρ a ξ := rfl

/-- **Representation on its essential subspace.** Let `H` be a complete complex Hilbert space and let
`A` be a nonunital, possibly nonassociative semiring with a distributive complex scalar action and a
star operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars, and star.
Restricting each `ρ(a)` to the closed essential subspace gives a representation of `A` on that
Hilbert space. -/
def essentialRepresentation (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₙₐ[ℂ] (ρ.essentialSpace →L[ℂ] ρ.essentialSpace) where
  toFun := ρ.essentialOperator
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply Subtype.ext
    change ρ 0 (ξ : H) = 0
    simp only [map_zero, _root_.zero_apply]
  map_add' := by
    intro a b
    apply ContinuousLinearMap.ext
    intro ξ
    apply Subtype.ext
    change ρ (a + b) (ξ : H) = ρ a ξ + ρ b ξ
    simp only [map_add, _root_.add_apply]
  map_smul' := by
    intro c a
    apply ContinuousLinearMap.ext
    intro ξ
    apply Subtype.ext
    change ρ (c • a) (ξ : H) = c • ρ a ξ
    simp only [map_smul, _root_.smul_apply]
  map_mul' := by
    intro a b
    apply ContinuousLinearMap.ext
    intro ξ
    apply Subtype.ext
    change ρ (a * b) (ξ : H) = ρ a (ρ b ξ)
    simp only [map_mul, _root_.mul_apply_eq_comp]
  map_star' := by
    intro a
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro ξ η
    change ⟪ρ (star a) (ξ : H), (η : H)⟫_ℂ = ⟪(ξ : H), ρ a (η : H)⟫_ℂ
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- **Values of the essential representation.** Let `H` be a complete complex Hilbert space and let `A`
be a nonunital, possibly nonassociative semiring with a distributive complex scalar action and a
star operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars, and star. For
`a ∈ A` and `ξ` in the essential subspace, the restricted representation evaluates to the same
ambient vector `ρ(a)ξ`. -/
@[simp]
theorem essentialRepresentation_apply_coe (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A)
    (ξ : ρ.essentialSpace) :
    (ρ.essentialRepresentation a ξ : H) = ρ a ξ := rfl

/-- **Kernel of the essential restriction.** Let `H` be a complete complex Hilbert space and let `A` be
a nonunital, possibly nonassociative semiring with a distributive complex scalar action and a star
operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars, and star. For
every `a ∈ A`, its operator in the essential representation is zero exactly when `ρ(a) = 0` on `H`. -/
theorem essentialRepresentation_eq_zero_iff (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    ρ.essentialRepresentation a = 0 ↔ ρ a = 0 := by
  constructor
  · intro h
    have hp : ρ a * star (ρ a) = 0 := by
      apply ContinuousLinearMap.ext
      intro ξ
      have hvalue := congrArg
        (fun T : ρ.essentialSpace →L[ℂ] ρ.essentialSpace =>
          ((T ⟨ρ (star a) ξ, ρ.range_mem_essentialSpace (star a) ξ⟩ : ρ.essentialSpace) : H)) h
      change ρ a (ρ (star a) ξ) = 0 at hvalue
      change ρ a ((star (ρ a)) ξ) = 0
      rw [← map_star]
      exact hvalue
    have hn : ‖ρ a‖ * ‖ρ a‖ = 0 := by
      rw [← CStarRing.norm_self_mul_star, hp, norm_zero]
    exact norm_eq_zero.mp (mul_self_eq_zero.mp hn)
  · intro h
    apply ContinuousLinearMap.ext
    intro ξ
    apply Subtype.ext
    change ρ a (ξ : H) = 0
    rw [h]
    rfl

/-- **Nondegeneracy of the essential restriction.** Let `H` be a complete complex Hilbert space and let
`A` be a nonunital, possibly nonassociative semiring with a distributive complex scalar action and a
star operation. Let `ρ : A → B(H)` preserve addition, multiplication, complex scalars, and star. The
complex-linear span of the ranges of all operators in the essential representation is dense in its
Hilbert space. -/
theorem nondegenerate_essentialRepresentation (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    Dense (Submodule.span ℂ (Set.range fun p : A × ρ.essentialSpace =>
      ρ.essentialRepresentation p.1 p.2) : Set ρ.essentialSpace) := by
  let S : Submodule ℂ ρ.essentialSpace := Submodule.span ℂ
    (Set.range fun p : A × ρ.essentialSpace => ρ.essentialRepresentation p.1 p.2)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply S.topologicalClosure_eq_top_iff.mpr
  apply eq_bot_iff.mpr
  intro v hv
  apply Subtype.ext
  have hkill : ∀ a : A, ρ a (v : H) = 0 := by
    intro a
    have hi := hv (ρ.essentialRepresentation (star a)
      ⟨ρ a (v : H), ρ.range_mem_essentialSpace a v⟩)
      (Submodule.subset_span ⟨(star a,
        ⟨ρ a (v : H), ρ.range_mem_essentialSpace a v⟩), rfl⟩)
    change ⟪ρ (star a) (ρ a (v : H)), (v : H)⟫_ℂ = 0 at hi
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at hi
    exact inner_self_eq_zero.mp hi
  let P : Submodule ℂ H := (innerSL ℂ (v : H)).ker
  have hspan : Submodule.span ℂ (Set.range fun p : A × H => ρ p.1 p.2) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, ξ⟩, rfl⟩
    change ⟪(v : H), ρ a ξ⟫_ℂ = 0
    rw [← ContinuousLinearMap.adjoint_inner_left (ρ a) ξ (v : H),
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star, hkill (star a), inner_zero_left]
  have hspace : ρ.essentialSpace ≤ P :=
    (Submodule.span ℂ (Set.range fun p : A × H => ρ p.1 p.2)).topologicalClosure_minimal
      hspan (innerSL ℂ (v : H)).isClosed_ker
  have hinner : ⟪(v : H), (v : H)⟫_ℂ = 0 := hspace v.property
  exact inner_self_eq_zero.mp hinner


end Algebraic

section AdditiveGroup

variable {A : Type uA} [NonUnitalNonAssocRing A] [DistribMulAction ℂ A] [Star A]

/-- **Faithfulness of the essential restriction.** Let `A` be a nonunital, possibly nonassociative ring
with a distributive complex scalar action and a star operation, and let `H` be a complete complex
Hilbert space. An injective complex star representation `ρ : A → B(H)` remains injective when
restricted to its closed essential subspace. -/
theorem injective_essentialRepresentation (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hρ : Function.Injective ρ) : Function.Injective ρ.essentialRepresentation := by
  intro a b hab
  apply hρ
  have hz : ρ.essentialRepresentation (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hzero : ρ (a - b) = 0 := (ρ.essentialRepresentation_eq_zero_iff (a - b)).mp hz
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

end AdditiveGroup

section CStarNorm

variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- **Norm of a faithful essential representation.** For a nonunital complex C*-algebra `A`, a complete
complex Hilbert space `H`, and an injective nonunital complex star homomorphism `ρ : A → B(H)`, the
operator of `a ∈ A` on the closed essential subspace of `ρ` has norm `‖a‖`. -/
theorem norm_essentialRepresentation (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hρ : Function.Injective ρ) (a : A) : ‖ρ.essentialRepresentation a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map ρ.essentialRepresentation (ρ.injective_essentialRepresentation hρ) a

end CStarNorm

end NonUnitalStarAlgHom

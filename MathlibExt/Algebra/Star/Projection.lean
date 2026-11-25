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

/-!
# Bundled star projections

This file supplies a minimal bundled carrier for star projections, its action
under nonunital star-algebra homomorphisms, and Murray--von Neumann
equivalence.  The mathematical predicate and its mapping theorem remain
Mathlib's `IsStarProjection`; no algebraic instances are installed on the
bundled subtype.
-/

@[expose] public section

universe u v w

/-- Let `A` be a type with multiplication and a star operation. A bundled star projection is an element
`p` satisfying `p*p = p` and `star p = p`.
-/
abbrev StarProjection (A : Type u) [Mul A] [Star A] :=
  {p : A // IsStarProjection p}

namespace StarProjection

variable {A : Type u} {B : Type v} {C : Type w}

/-- Let `A` be a type with multiplication and a star operation. An element satisfying `p*p = p` and
`star p = p` defines a star projection.
-/
def mk [Mul A] [Star A] (p : A) (hp : IsStarProjection p) : StarProjection A :=
  ⟨p, hp⟩

@[simp]
theorem coe_mk [Mul A] [Star A] (p : A) (hp : IsStarProjection p) :
    ((mk p hp : StarProjection A) : A) = p :=
  rfl

@[simp]
theorem isStarProjection [Mul A] [Star A] (p : StarProjection A) :
    IsStarProjection (p : A) :=
  p.property

@[ext]
theorem ext [Mul A] [Star A] {p q : StarProjection A}
    (h : (p : A) = (q : A)) : p = q :=
  Subtype.ext h

theorem coe_injective [Mul A] [Star A] :
    Function.Injective (fun p : StarProjection A ↦ (p : A)) :=
  Subtype.coe_injective

/-- Let `A` be a possibly nonunital, nonassociative semiring with an additive star involution. Its zero
element is a star projection.
-/
def zero (A : Type u) [NonUnitalNonAssocSemiring A] [StarAddMonoid A] :
    StarProjection A :=
  ⟨0, IsStarProjection.zero A⟩

@[simp]
theorem coe_zero (A : Type u) [NonUnitalNonAssocSemiring A] [StarAddMonoid A] :
    ((zero A : StarProjection A) : A) = 0 :=
  rfl

/-- Let `A` carry multiplication with a two-sided identity and a multiplication-reversing star
involution. Its identity is a star projection.
-/
def one (A : Type u) [MulOneClass A] [StarMul A] : StarProjection A :=
  ⟨1, IsStarProjection.one A⟩

@[simp]
theorem coe_one (A : Type u) [MulOneClass A] [StarMul A] :
    ((one A : StarProjection A) : A) = 1 :=
  rfl

/-! ## Homomorphic images -/

/-- Let a monoid `R` act additively on possibly nonunital, nonassociative semirings `A` and `B` with
star operations. A homomorphism preserving these structures sends each bundled star projection of
`A` to one of `B`.
-/
def map
    {R : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    (f : A →⋆ₙₐ[R] B) (p : StarProjection A) : StarProjection B :=
  ⟨f p, p.property.map f⟩

@[simp]
theorem coe_map
    {R : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    (f : A →⋆ₙₐ[R] B) (p : StarProjection A) :
    ((map f p : StarProjection B) : B) = f (p : A) :=
  rfl

@[simp]
theorem map_id
    {R : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    (p : StarProjection A) :
    map (NonUnitalStarAlgHom.id R A) p = p := by
  ext
  rfl

@[simp]
theorem map_comp
    {R : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
    [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]
    (f : A →⋆ₙₐ[R] B) (g : B →⋆ₙₐ[R] C) (p : StarProjection A) :
    map (g.comp f) p = map g (map f p) := by
  ext
  rfl

/-! ## Murray--von Neumann equivalence -/

/-- Let `A` be a semigroup with a multiplication-reversing star involution. Bundled star projections
`p`, `q` are Murray--von Neumann equivalent if there exists `v ∈ A` with `p = star v * v` and `q = v
* star v`.
-/
def MurrayVonNeumannEquivalent
    [Semigroup A] [StarMul A]
    (p q : StarProjection A) : Prop :=
  ∃ v : A, (p : A) = star v * v ∧ (q : A) = v * star v

theorem murrayVonNeumannEquivalent_refl
    [Semigroup A] [StarMul A]
    (p : StarProjection A) : MurrayVonNeumannEquivalent p p := by
  refine ⟨p, ?_, ?_⟩
  · rw [p.property.isSelfAdjoint.star_eq]
    exact p.property.isIdempotentElem.eq.symm
  · rw [p.property.isSelfAdjoint.star_eq]
    exact p.property.isIdempotentElem.eq.symm

theorem murrayVonNeumannEquivalent_symm
    [Semigroup A] [StarMul A]
    {p q : StarProjection A}
    (h : MurrayVonNeumannEquivalent p q) :
    MurrayVonNeumannEquivalent q p := by
  obtain ⟨v, hp, hq⟩ := h
  refine ⟨star v, ?_, ?_⟩
  · simpa using hq
  · simpa using hp

theorem murrayVonNeumannEquivalent_trans
    [Semigroup A] [StarMul A]
    {p q r : StarProjection A}
    (hpq : MurrayVonNeumannEquivalent p q)
    (hqr : MurrayVonNeumannEquivalent q r) :
    MurrayVonNeumannEquivalent p r := by
  obtain ⟨u, hp, hq₁⟩ := hpq
  obtain ⟨v, hq₂, hr⟩ := hqr
  refine ⟨v * u, ?_, ?_⟩
  · calc
      (p : A) = star u * u := hp
      _ = (star u * u) * (star u * u) := by
        rw [← hp]
        exact p.property.isIdempotentElem.eq.symm
      _ = star u * ((u * star u) * u) := by simp only [mul_assoc]
      _ = star u * ((star v * v) * u) := by rw [← hq₁, hq₂]
      _ = star (v * u) * (v * u) := by simp [mul_assoc]
  · calc
      (r : A) = v * star v := hr
      _ = (v * star v) * (v * star v) := by
        rw [← hr]
        exact r.property.isIdempotentElem.eq.symm
      _ = v * ((star v * v) * star v) := by simp only [mul_assoc]
      _ = v * ((u * star u) * star v) := by rw [← hq₂, hq₁]
      _ = (v * u) * star (v * u) := by simp [mul_assoc]

theorem murrayVonNeumannEquivalent_equivalence
    (A : Type u) [Semigroup A] [StarMul A] :
    Equivalence
      (MurrayVonNeumannEquivalent : StarProjection A → StarProjection A → Prop) :=
  ⟨murrayVonNeumannEquivalent_refl,
    fun {_ _} h ↦ murrayVonNeumannEquivalent_symm h,
    fun {_ _ _} h₁ h₂ ↦ murrayVonNeumannEquivalent_trans h₁ h₂⟩

/-- Let a monoid `R` act additively on possibly nonunital semirings `A`, `B` with
multiplication-reversing star involutions. A structure-preserving homomorphism `f : A →⋆ₙₐ[R] B`
sends Murray--von Neumann equivalent projections to equivalent projections, with witness `f v`.
-/
theorem MurrayVonNeumannEquivalent.map
    {R : Type*} [Monoid R]
    [NonUnitalSemiring A] [DistribMulAction R A] [StarMul A]
    [NonUnitalSemiring B] [DistribMulAction R B] [StarMul B]
    {p q : StarProjection A}
    (h : MurrayVonNeumannEquivalent p q) (f : A →⋆ₙₐ[R] B) :
    MurrayVonNeumannEquivalent (map f p) (map f q) := by
  obtain ⟨v, hp, hq⟩ := h
  refine ⟨f v, ?_, ?_⟩
  · calc
      ((StarProjection.map f p : StarProjection B) : B) = f (p : A) := rfl
      _ = f (star v * v) := congrArg f hp
      _ = star (f v) * f v := by rw [map_mul, map_star]
  · calc
      ((StarProjection.map f q : StarProjection B) : B) = f (q : A) := rfl
      _ = f (v * star v) := congrArg f hq
      _ = f v * star (f v) := by rw [map_mul, map_star]

end StarProjection

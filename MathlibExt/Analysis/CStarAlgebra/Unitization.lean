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

public import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# The scalar projection from a C-star unitization

This file bundles the scalar-coordinate projection from the unitization of a
complex nonunital C-star algebra as a star algebra homomorphism.  The
projection is natural for the canonical unitization of nonunital star algebra
homomorphisms.
-/

@[expose] public section

namespace Unitization

universe u v

/-- **Scalar projection from a C*-unitization.** For a nonunital complex C*-algebra `A`, the map `(λ,a)
↦ λ` from its complex unitization to `ℂ` is a unital complex star-algebra homomorphism. -/
def fstStarAlgHom (A : Type u) [NonUnitalCStarAlgebra A] :
    Unitization ℂ A →⋆ₐ[ℂ] ℂ where
  toAlgHom := Unitization.fstHom ℂ A
  map_star' := Unitization.fst_star

@[simp]
theorem fstStarAlgHom_apply
    (A : Type u) [NonUnitalCStarAlgebra A] (x : Unitization ℂ A) :
    fstStarAlgHom A x = x.fst :=
  rfl

@[simp]
theorem fstStarAlgHom_inl
    (A : Type u) [NonUnitalCStarAlgebra A] (z : ℂ) :
    fstStarAlgHom A (Unitization.inl z) = z := by
  simp

@[simp]
theorem fstStarAlgHom_inr
    (A : Type u) [NonUnitalCStarAlgebra A] (a : A) :
    fstStarAlgHom A (Unitization.inr a) = 0 := by
  simp

/-- **Naturality of the unitization scalar projection.** Let `A,B` be nonunital complex C*-algebras and
`φ : A → B` a nonunital complex star homomorphism. Scalar projection after unitizing `φ` is the
scalar projection of the source unitization. -/
@[simp]
theorem fstStarAlgHom_comp_starMap
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : A →⋆ₙₐ[ℂ] B) :
    (fstStarAlgHom B).comp (Unitization.starMap phi) = fstStarAlgHom A := by
  apply StarAlgHom.ext
  intro x
  induction x using Unitization.ind with
  | inl_add_inr z a =>
      simp [Unitization.algebraMap_eq_inl]

/-- **Scalar coordinate under unitization.** Let `A,B` be nonunital complex C*-algebras and `φ : A → B`
a nonunital complex star homomorphism. For an element `(λ,a)` of the source unitization, its image
under the unitized map has scalar coordinate `λ`. -/
theorem starMap_fst
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : A →⋆ₙₐ[ℂ] B) (x : Unitization ℂ A) :
    (Unitization.starMap phi x).fst = x.fst := by
  change fstStarAlgHom B (Unitization.starMap phi x) = fstStarAlgHom A x
  exact DFunLike.congr_fun (fstStarAlgHom_comp_starMap phi) x

/-- **Algebra coordinate under unitization.** Let `A,B` be nonunital complex C*-algebras and `φ : A → B`
a nonunital complex star homomorphism. For an element `(λ,a)` of the source unitization, its image
under the unitized map has algebra coordinate `φ(a)`. -/
theorem starMap_snd
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : A →⋆ₙₐ[ℂ] B) (x : Unitization ℂ A) :
    (Unitization.starMap phi x).snd = phi x.snd := by
  induction x using Unitization.ind with
  | inl_add_inr z a =>
      simp only [map_add, Unitization.starMap_inl, Unitization.starMap_inr,
        Unitization.algebraMap_eq_inl, Unitization.snd_add,
        Unitization.snd_inl, Unitization.snd_inr, zero_add]

end Unitization

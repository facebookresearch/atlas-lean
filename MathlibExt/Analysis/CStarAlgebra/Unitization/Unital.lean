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

public import MathlibExt.Analysis.CStarAlgebra.Unitization
public import MathlibExt.Algebra.Algebra.Unitization.Unital

/-!
# Unitization of a unital C-star algebra

The canonical unitization of a unital complex C-star algebra is star-algebra
equivalent to the product of the scalars and the original algebra.
-/

@[expose] public section

open scoped CStarAlgebra

namespace Unitization

noncomputable section

universe u v

/-- **Product map from a unital algebra unitization.** Let `A` be a unital complex C*-algebra. The map
`(λ,a) ↦ (λ, λ 1_A + a)` is a unital complex star homomorphism from the complex unitization of `A`
to `ℂ × A`. -/
def unitalProdStarAlgHom
    (A : Type u) [CStarAlgebra A] :
    Unitization ℂ A →⋆ₐ[ℂ] ℂ × A where
  __ := Unitization.unitalProdAlgHom ℂ A
  map_star' := by
    intro x
    change
      ((fstStarAlgHom A).prod
          (Unitization.starLift (NonUnitalStarAlgHom.id ℂ A))) (star x) =
        star (((fstStarAlgHom A).prod
          (Unitization.starLift (NonUnitalStarAlgHom.id ℂ A))) x)
    exact map_star _ x

@[simp]
theorem unitalProdStarAlgHom_apply
    (A : Type u) [CStarAlgebra A] (x : Unitization ℂ A) :
    unitalProdStarAlgHom A x =
      (x.fst, x.fst • (1 : A) + x.snd) := by
  change Unitization.unitalProdAlgHom ℂ A x = _
  exact Unitization.unitalProdAlgHom_apply ℂ A x

/-- **Product equivalence for a unital algebra unitization.** Let `A` be a unital complex C*-algebra.
The complex unitization of `A` is star-algebra equivalent to `ℂ × A` by `(λ,a) ↦ (λ, λ 1_A + a)`. -/
noncomputable def unitalProdStarAlgEquiv
    (A : Type u) [CStarAlgebra A] :
    Unitization ℂ A ≃⋆ₐ[ℂ] ℂ × A :=
  StarAlgEquiv.ofAlgEquiv (Unitization.unitalProdAlgEquiv ℂ A) fun x => by
    change unitalProdStarAlgHom A (star x) = star (unitalProdStarAlgHom A x)
    exact map_star _ x

/-- **Forward formula for the unitization product equivalence.** Let `A` be a unital complex C*-algebra.
The product equivalence sends an element `(λ,a)` of the unitization to `(λ, λ 1_A + a)`. -/
@[simp]
theorem unitalProdStarAlgEquiv_apply
    (A : Type u) [CStarAlgebra A] (x : Unitization ℂ A) :
    unitalProdStarAlgEquiv A x =
      (x.fst, x.fst • (1 : A) + x.snd) := by
  change Unitization.unitalProdAlgEquiv ℂ A x = _
  exact Unitization.unitalProdAlgEquiv_apply ℂ A x

/-- **Inverse formula for the unitization product equivalence.** Let `A` be a unital complex C*-algebra.
The inverse product equivalence sends `(λ,b) ∈ ℂ × A` to `(λ, b - λ 1_A)` in the unitization. -/
@[simp]
theorem unitalProdStarAlgEquiv_symm_apply
    (A : Type u) [CStarAlgebra A] (x : ℂ × A) :
    (unitalProdStarAlgEquiv A).symm x =
      Unitization.inl x.1 +
        Unitization.inr (R := ℂ) (A := A) (x.2 - x.1 • (1 : A)) := by
  change (Unitization.unitalProdAlgEquiv ℂ A).symm x = _
  exact Unitization.unitalProdAlgEquiv_symm_apply ℂ A x

/-- **Naturality of the unitization product equivalence.** For unital complex C*-algebras `A,B` and a
unital complex star homomorphism `φ : A → B`, the unitized homomorphism corresponds, under the
canonical equivalences with `ℂ × A` and `ℂ × B`, to the product map `(λ,a) ↦ (λ,φ(a))`. -/
theorem unitalProdStarAlgEquiv_naturality
    {A : Type u} {B : Type v}
    [CStarAlgebra A] [CStarAlgebra B]
    (phi : A →⋆ₐ[ℂ] B) :
    (unitalProdStarAlgEquiv B).toStarAlgHom.comp
        (Unitization.starMap phi.toNonUnitalStarAlgHom) =
      ((StarAlgHom.fst ℂ ℂ A).prod
        (phi.comp (StarAlgHom.snd ℂ ℂ A))).comp
          (unitalProdStarAlgEquiv A).toStarAlgHom := by
  apply StarAlgHom.ext
  intro x
  induction x using Unitization.ind with
  | inl_add_inr c a =>
      apply Prod.ext <;>
        simp [Unitization.algebraMap_eq_inl]

end

end Unitization

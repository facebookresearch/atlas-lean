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

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Coefficient postcomposition on bounded continuous functions

Nonunital complex C-star homomorphisms act pointwise on bounded continuous
functions. Contractivity supplies the required global Lipschitz bound.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

namespace BoundedContinuousFunction

universe uX uA uB uC

private theorem nonUnitalStarAlgHom_lipschitz
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) : LipschitzWith 1 φ := by
  refine AddMonoidHomClass.lipschitz_of_bound_nnnorm φ 1 ?_
  intro a
  simpa only [one_mul] using
    NonUnitalStarAlgHom.nnNorm_apply_le φ a

/-- Let `X` be a topological space. Let `A`, `B` be possibly nonunital complex C*-algebras.

Pointwise coefficient postcomposition on bounded continuous functions. -/
@[no_expose]
def compNonUnitalStarAlgHom
    {X : Type uX} [TopologicalSpace X]
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) : (X →ᵇ A) →⋆ₙₐ[ℂ] (X →ᵇ B) where
  toFun f := f.comp φ (nonUnitalStarAlgHom_lipschitz φ)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_smul' z f := ext fun x => map_smul φ z (f x)
  map_star' f := ext fun x => map_star φ (f x)

@[simp]
theorem compNonUnitalStarAlgHom_apply
    {X : Type uX} [TopologicalSpace X]
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) (f : X →ᵇ A) (x : X) :
    compNonUnitalStarAlgHom φ f x = φ (f x) := by
  rfl

@[simp]
theorem compNonUnitalStarAlgHom_id
    (X : Type uX) [TopologicalSpace X]
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    compNonUnitalStarAlgHom
        (X := X) (NonUnitalStarAlgHom.id ℂ A) =
      NonUnitalStarAlgHom.id ℂ (X →ᵇ A) := by
  ext f x
  rfl

@[simp]
theorem compNonUnitalStarAlgHom_zero
    (X : Type uX) [TopologicalSpace X]
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    compNonUnitalStarAlgHom
        (X := X) (0 : A →⋆ₙₐ[ℂ] B) = 0 := by
  ext f x
  rfl

/-- Let `X` be a topological space. Let `A`, `B`, `C` be possibly nonunital complex C*-algebras.

Bounded coefficient postcomposition respects composition. -/
theorem compNonUnitalStarAlgHom_comp
    {X : Type uX} [TopologicalSpace X]
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] C) :
    compNonUnitalStarAlgHom (X := X) (ψ.comp φ) =
      (compNonUnitalStarAlgHom ψ).comp
        (compNonUnitalStarAlgHom φ) := by
  ext f x
  rfl

#print axioms compNonUnitalStarAlgHom
#print axioms compNonUnitalStarAlgHom_apply
#print axioms compNonUnitalStarAlgHom_id
#print axioms compNonUnitalStarAlgHom_zero
#print axioms compNonUnitalStarAlgHom_comp

end BoundedContinuousFunction

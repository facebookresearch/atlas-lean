/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap

public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Nonunital coefficient homs on continuous functions

These public coefficient maps provide point evaluation and postcomposition for
any topological domain, without a unit or compactness hypothesis. Continuity of
the supplied complex C-star hom is the existing theorem, not an extra
output-map assumption.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra

namespace ContinuousMap

universe uX uA uB uC

/-- Let `X` be a topological space and let `A` be a possibly nonunital complex C*-algebra.

Evaluation of continuous functions at a point as a nonunital complex star algebra homomorphism. -/
def evalNonUnitalStarAlgHom
    {X : Type uX} [TopologicalSpace X]
    {A : Type uA} [NonUnitalCStarAlgebra A] (x : X) :
    C(X, A) →⋆ₙₐ[ℂ] A where
  toFun f := f x
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem evalNonUnitalStarAlgHom_apply
    {X : Type uX} [TopologicalSpace X]
    {A : Type uA} [NonUnitalCStarAlgebra A]
    (x : X) (f : C(X, A)) :
    evalNonUnitalStarAlgHom (A := A) x f = f x :=
  rfl

variable (X : Type uX) [TopologicalSpace X]
variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- Let `X` be a topological space and let `A` and `B` be possibly nonunital complex C*-algebras.

Pointwise coefficient postcomposition by a nonunital star hom. -/
def compNonUnitalStarAlgHom (g : A →⋆ₙₐ[ℂ] B) :
    C(X, A) →⋆ₙₐ[ℂ] C(X, B) where
  toFun f := ⟨fun x => g (f x),
    ((NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
      (F := A →⋆ₙₐ[ℂ] B) (A := A) (B := B)).toContinuousMapClass.map_continuous g).comp
      f.continuous⟩
  map_zero' := by ext x; exact map_zero g
  map_add' f h := by ext x; exact map_add g (f x) (h x)
  map_smul' z f := by ext x; exact map_smul g z (f x)
  map_mul' f h := by ext x; exact map_mul g (f x) (h x)
  map_star' f := by ext x; exact map_star g (f x)

@[simp]
theorem compNonUnitalStarAlgHom_apply (g : A →⋆ₙₐ[ℂ] B)
    (f : C(X, A)) (x : X) : compNonUnitalStarAlgHom X g f x = g (f x) := by
  rfl

@[simp]
theorem compNonUnitalStarAlgHom_id :
    compNonUnitalStarAlgHom X (NonUnitalStarAlgHom.id ℂ A) =
      NonUnitalStarAlgHom.id ℂ C(X, A) := by
  ext f x
  rfl

theorem compNonUnitalStarAlgHom_comp
    (g : A →⋆ₙₐ[ℂ] B) (h : B →⋆ₙₐ[ℂ] C) :
    compNonUnitalStarAlgHom X (h.comp g) =
      (compNonUnitalStarAlgHom X h).comp (compNonUnitalStarAlgHom X g) := by
  ext f x
  rfl

end ContinuousMap

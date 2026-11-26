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

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Hom adjunction for an algebra tensor factor

Let R be a commutative semiring, A an R-algebra, V an R-module and M an A-module with a
compatible R-action commuting with the A-action. The R-linear equivalence Hom_A(A⊗_R
V,M)≃Hom_R(V,M) sends F to v↦F(1⊗v), with inverse g↦(a⊗v↦a•g(v)). A may be noncommutative.
-/

@[expose] public section

noncomputable section

universe u v w z

open scoped TensorProduct

namespace TensorProduct

variable (R : Type u) [CommSemiring R] (A : Type v) [Semiring A] [Algebra R A]
  (V : Type w) [AddCommMonoid V] [Module R V]
  (M : Type z) [AddCommMonoid M] [Module R M] [Module A M]
  [IsScalarTower R A M] [SMulCommClass A R M]

local instance : SMulCommClass R A M := SMulCommClass.symm A R M

/-- **Ground-linear Hom cancellation of an algebra factor.**

Let R be a commutative semiring, A an R-algebra, V an R-module and M an A-module with
compatible commuting R,A scalar actions. The equivalence algebraTensorHomEquiv R A V
M:Hom_A(A⊗_R V,M)≃ₗ[R]Hom_R(V,M) is F↦(v↦F(1⊗v)), with inverse g acting by a⊗v↦a•g(v).
-/
def algebraTensorHomEquiv : (A ⊗[R] V →ₗ[A] M) ≃ₗ[R] (V →ₗ[R] M) :=
  (AlgebraTensorModule.lift.equiv R A R A V M).symm.trans
    (LinearMap.ringLmapEquivSelf A R (V →ₗ[R] M))

@[simp]
theorem algebraTensorHomEquiv_apply (f : A ⊗[R] V →ₗ[A] M) (v : V) :
    algebraTensorHomEquiv R A V M f v = f ((1 : A) ⊗ₜ[R] v) := rfl

@[simp]
theorem algebraTensorHomEquiv_symm_tmul (f : V →ₗ[R] M) (a : A) (v : V) :
    (algebraTensorHomEquiv R A V M).symm f (a ⊗ₜ[R] v) = a • f v := rfl

end TensorProduct

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Ground-linear Hom cancellation of an algebra tensor factor

The acting algebra may be noncommutative. The native heterobasic tensor
universal property, followed by native evaluation at the algebra unit,
gives the ground-linear Hom equivalence. This is distinct from the
commutative-acting-ring `LinearMap.liftBaseChangeEquiv`.
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

/-- Actual Hom cancellation, linear over the ground semiring and valid for an
arbitrary acting algebra. -/
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

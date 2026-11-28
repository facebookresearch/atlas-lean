/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Hom cancellation for an algebra tensor factor

Let R be a commutative semiring, A an arbitrary R-algebra semiring and V an R-semimodule. Let M
carry R- and A-actions compatible with the scalar tower R→A. Then Hom_A(A⊗_RV,M) is
R-linearly equivalent to Hom_R(V,M).

The forward map evaluates an A-linear tensor map at 1⊗v. The inverse takes an R-linear map g:V→M
to a⊗v ↦ a·g(v). This uses the coefficient action on M and the left A-action on the tensor's
A-factor; no A-action on V or commutativity of A is needed. R,A,V,M may occupy separate
universes.
-/

@[expose] public section

noncomputable section

universe u v w z

open scoped TensorProduct

namespace TensorProduct

variable (R : Type u) [CommSemiring R] (A : Type v) [Semiring A] [Algebra R A]
  (V : Type w) [AddCommMonoid V] [Module R V]
  (M : Type z) [AddCommMonoid M] [Module R M] [Module A M]
  [IsScalarTower R A M]

/-- Let R be a commutative semiring, A an R-algebra semiring, V an R-semimodule and M a semimodule
with R,A-actions and scalar tower compatibility. There is an R-linear equivalence
Hom_A(A⊗_RV,M) ≃ Hom_R(V,M), sending f to v ↦ f(1⊗v) and g inversely to a⊗v ↦ a·g(v). The acting
A may be noncommutative and all four universes are arbitrary. -/
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

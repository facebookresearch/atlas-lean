/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Scalar restriction of alternating maps

Let R be a commutative semiring, S an R-algebra, and M,N modules over both R and S with
compatible scalar towers r•x=(algebraMap R S r)•x. An S-alternating map on M indexed by any
type I is R-alternating with the same values.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace AlternatingMap

variable {R : Type u} {S : Type v}
variable [CommSemiring R] [Semiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module S M]
  [IsScalarTower R S M]
variable {N : Type z} [AddCommMonoid N] [Module R N] [Module S N]
  [IsScalarTower R S N]
variable {ι : Type*}

/-- **Alternating map over the base semiring.**

Let R be a commutative semiring, S a semiring with an R-algebra structure, and M,N additive
commutative monoids with compatible R,S-module structures. For an S-alternating map f:M^I→N,
restrictScalars f is the R-alternating map with value f(v) for every family v:I→M.
-/
def restrictScalars (f : M [⋀^ι]→ₗ[S] N) : M [⋀^ι]→ₗ[R] N :=
  { f.toMultilinearMap.restrictScalars R with
    map_eq_zero_of_eq' := f.map_eq_zero_of_eq }

@[simp]
theorem coe_restrictScalars (f : M [⋀^ι]→ₗ[S] N) :
    ⇑(f.restrictScalars (R := R)) = f :=
  rfl

@[simp]
theorem restrictScalars_apply (f : M [⋀^ι]→ₗ[S] N) (a : ι → M) :
    f.restrictScalars (R := R) a = f a :=
  rfl

end AlternatingMap

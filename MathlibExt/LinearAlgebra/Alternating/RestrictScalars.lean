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
# Restriction of scalars for alternating maps

An alternating map over an algebra is also alternating over the base ring
when the source and target scalar actions form scalar towers.
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

/-- Restrict the scalars of an alternating map along an algebra. -/
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

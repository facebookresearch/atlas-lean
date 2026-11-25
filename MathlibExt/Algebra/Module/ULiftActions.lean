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

public import Mathlib.Algebra.Module.ULift

/-!
# Commutation of lifted actions

The inherited actions on `ULift M` commute whenever the actions on M
commute. The scalar actions are those supplied by Mathlib.
-/

@[expose] public section

universe u v w z t

namespace ULift

/-- The actual inherited lift of two commuting actions still commutes. -/
theorem smulCommClassOfBase (R : Type u) (S : Type v) (M : Type w)
    [SMul R M] [SMul S M] [SMulCommClass R S M] :
    SMulCommClass R S (ULift.{z} M) :=
  ⟨fun r s m => ULift.ext (smul_comm r s m.down)⟩

/-- Canonical commutation capability for the existing native lifted actions. -/
instance instSMulCommClassOfBase (R : Type u) (S : Type v) (M : Type w)
    [SMul R M] [SMul S M] [SMulCommClass R S M] :
    SMulCommClass R S (ULift.{z} M) :=
  smulCommClassOfBase R S M

/-- Native up-f-down as a linear map between independently lifted carriers. -/
def mapLinear (R : Type u) [Semiring R]
    {M : Type v} {N : Type w} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) : ULift.{z} M →ₗ[R] ULift.{t} N :=
  (ULift.moduleEquiv : ULift.{t} N ≃ₗ[R] N).symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv : ULift.{z} M ≃ₗ[R] M).toLinearMap)

/-- The lifted linear map has the actual original value. -/
theorem mapLinear_apply (R : Type u) [Semiring R]
    {M : Type v} {N : Type w} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (m : ULift.{z} M) :
    mapLinear R f m = ULift.up (f m.down) := rfl

end ULift

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
# Commuting actions and linear maps on lifted carriers

Suppose types R and S act on a type M and the two actions commute.
Their induced actions on ULift M also commute, since each action is applied
to the underlying element of M. The scalar, carrier, and lift universes
are independent; no algebraic structure on R or S is needed for this assertion.

For a semiring R and R-modules M, N, an R-linear map f : M → N induces
an R-linear map ULift M → ULift N. On an element with underlying value m,
the lifted map has underlying value f(m), allowing separate lifts of M and N.
-/

@[expose] public section

universe u v w z t

namespace ULift

/-- Let types R and S act on a type M, with r • (s • m) = s • (r • m)
for all r, s and m. The induced actions on ULift M satisfy the same
commutation law. R, S, M and the lift may have independent universes;
no multiplication on either scalar type is assumed. -/
theorem smulCommClassOfBase (R : Type u) (S : Type v) (M : Type w)
    [SMul R M] [SMul S M] [SMulCommClass R S M] :
    SMulCommClass R S (ULift.{z} M) :=
  ⟨fun r s m => ULift.ext (smul_comm r s m.down)⟩

/-- For commuting actions of types R and S on M, the induced R- and
S-actions on ULift M commute. This supplies the commutation structure for
the lifted carrier with the same law r • (s • x) = s • (r • x).
The scalar and carrier universes, and the lift height, are independent. -/
instance instSMulCommClassOfBase (R : Type u) (S : Type v) (M : Type w)
    [SMul R M] [SMul S M] [SMulCommClass R S M] :
    SMulCommClass R S (ULift.{z} M) :=
  smulCommClassOfBase R S M

/-- Let R be a semiring, M and N R-modules, and f : M →ₗ[R] N an
R-linear map. This is the R-linear map ULift M →ₗ[R] ULift N which sends
the lift of m to the lift of f(m). The two module carriers and their
two lift heights may all be independent. -/
def mapLinear (R : Type u) [Semiring R]
    {M : Type v} {N : Type w} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) : ULift.{z} M →ₗ[R] ULift.{t} N :=
  (ULift.moduleEquiv : ULift.{t} N ≃ₗ[R] N).symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv : ULift.{z} M ≃ₗ[R] M).toLinearMap)

/-- For a semiring R, R-modules M and N, an R-linear map f : M → N,
and x ∈ ULift M, the lifted linear map satisfies
mapLinear(f)(x) = ULift.up(f(x.down)).
This formula holds for independent source and target lift heights. -/
theorem mapLinear_apply (R : Type u) [Semiring R]
    {M : Type v} {N : Type w} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (m : ULift.{z} M) :
    mapLinear R f m = ULift.up (f m.down) := rfl

end ULift

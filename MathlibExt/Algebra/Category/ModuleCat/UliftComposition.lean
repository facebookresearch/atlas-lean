/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.UliftCoherence

/-!
# Removing a module lift within its carrier universe

Let `R` be a ring and let an `R`-module `X` have carrier universe `max v w`. Lifting its
carrier by `ULift.{w}` remains within this universe.

The module equivalence `ULift.{w} X ≃ₗ[R] X` gives a natural isomorphism from the
corresponding lift functor to the identity. Its forward map sends `up(x)` to `x`, and its
inverse sends `x` to `up(x)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe r v w z

namespace ModuleCat

variable (R : Type r) [Ring R]

/-- The natural comparison for a module lift within its universe.

On `ModuleCat.{max v w} R`, lifting by `ULift.{w}` is naturally isomorphic to the identity
functor through the module equivalence `up(x) ↦ x`. -/
def uliftFunctorWithinIso :
    uliftFunctor.{w,max v w} R ≅ 𝟭 (ModuleCat.{max v w} R) :=
  NatIso.ofComponents (fun X => (ULift.moduleEquiv : ULift.{w} X ≃ₗ[R] X).toModuleIso) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x⟩
    rfl)

/-- The forward formula for an in-universe module lift.

The forward component of the lift comparison sends `ULift.up x` to `x`. -/
theorem uliftFunctorWithinIso_hom_up (X : ModuleCat.{max v w} R) (x : X) :
    ((uliftFunctorWithinIso.{r,v,w} R).hom.app X).hom (ULift.up x) = x := rfl

/-- The inverse formula for an in-universe module lift.

The inverse component of the lift comparison sends `x` to `ULift.up x`. -/
theorem uliftFunctorWithinIso_inv (X : ModuleCat.{max v w} R) (x : X) :
    ((uliftFunctorWithinIso.{r,v,w} R).inv.app X).hom x = ULift.up x := rfl

end ModuleCat

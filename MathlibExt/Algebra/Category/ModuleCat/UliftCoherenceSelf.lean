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

public import MathlibExt.Algebra.Category.ModuleCat.UliftCoherence

/-!
# Module lifts inside an existing carrier universe

For a ring `R : Type u`, a module carrier in universe `max ℓ v` already accommodates a lift by
`ℓ`. The module lift functor on that category is naturally isomorphic to the identity, with
forward map `x ↦ x.down` and inverse `x ↦ ULift.up x`.

At lift level zero this agrees with the zero-lift comparison. For two lift levels, flattening
the nested lifts and then lowering agrees with lowering the inner lift and then the outer
lift. The ring universe is independent of the carrier and lift universes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace ModuleCat

universe ℓ t v u

universe ℓ₁ v₁ u₁

/-- Contained module lift is naturally the identity.

For module carriers in universe `max ℓ v`, the functor `uliftFunctor.{ℓ,max ℓ v} R` is
naturally isomorphic to the identity. Each component is the module linear equivalence from
`ULift.{ℓ} M` to `M`. -/
def uliftFunctorSelfIso (R : Type u₁) [Ring R] :
    uliftFunctor.{ℓ₁, max ℓ₁ v₁} R ≅ 𝟭 (ModuleCat.{max ℓ₁ v₁} R) :=
  NatIso.ofComponents
    (fun M => (ULift.moduleEquiv : ULift.{ℓ₁} M ≃ₗ[R] M).toModuleIso) (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

/-- Forward contained-lift comparison lowers a module element.

At a module `M : ModuleCat.{max ℓ v} R`, the forward comparison sends `x : ULift.{ℓ} M` to
`x.down`. -/
theorem uliftFunctorSelfIso_hom_app_apply (R : Type u) [Ring R]
    (M : ModuleCat.{max ℓ v} R) (x : ULift.{ℓ} M) :
    ((uliftFunctorSelfIso.{ℓ, v} R).hom.app M).hom x = x.down := rfl

/-- Inverse contained-lift comparison lifts a module element.

At a module `M : ModuleCat.{max ℓ v} R`, the inverse comparison sends `x : M` to `ULift.up x`. -/
theorem uliftFunctorSelfIso_inv_app_apply (R : Type u) [Ring R]
    (M : ModuleCat.{max ℓ v} R) (x : M) :
    ((uliftFunctorSelfIso.{ℓ, v} R).inv.app M).hom x = ULift.up x := rfl

/-- Contained-lift comparison at zero agrees with the zero-lift isomorphism.

For lift level zero, `uliftFunctorSelfIso.{0,v} R` equals `uliftFunctorZeroIso.{v} R`. -/
theorem uliftFunctorSelfIso_zero (R : Type u) [Ring R] :
    uliftFunctorSelfIso.{0, v} R = uliftFunctorZeroIso.{v} R := rfl

/-- Contained-lift comparisons commute with nested-lift flattening.

For a module in universe `max ℓ t v`, flattening lifts by `ℓ` and `t` and then applying the
self-lift comparison equals applying the lift-by-`t` image of the inner self comparison and
then the outer self comparison. -/
theorem uliftFunctorSelfIso_comp (R : Type u) [Ring R]
    (M : ModuleCat.{max ℓ t v} R) :
    (uliftFunctorCompIso.{ℓ, t, max ℓ t v} R).hom.app M ≫
        (uliftFunctorSelfIso.{max ℓ t, v} R).hom.app M =
      (uliftFunctor.{t, max ℓ t v} R).map
          ((uliftFunctorSelfIso.{ℓ, max t v} R).hom.app M) ≫
        (uliftFunctorSelfIso.{t, max ℓ v} R).hom.app M := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end ModuleCat

end

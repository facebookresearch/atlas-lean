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
# Native module lifts already contained in the carrier universe

A lift level already contained in the source carrier world gives an actual
natural isomorphism to identity, with the original down/up coordinate maps.
The ring universe is independent. The existing zero and flattening
comparisons are retained.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace ModuleCat

universe ℓ t v u

universe ℓ₁ v₁ u₁

/-- A native module lift contained in its source carrier world is naturally identity. -/
def uliftFunctorSelfIso (R : Type u₁) [Ring R] :
    uliftFunctor.{ℓ₁, max ℓ₁ v₁} R ≅ 𝟭 (ModuleCat.{max ℓ₁ v₁} R) :=
  NatIso.ofComponents
    (fun M => (ULift.moduleEquiv : ULift.{ℓ₁} M ≃ₗ[R] M).toModuleIso) (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

/-- The forward comparison is the actual native coordinate lowering map. -/
theorem uliftFunctorSelfIso_hom_app_apply (R : Type u) [Ring R]
    (M : ModuleCat.{max ℓ v} R) (x : ULift.{ℓ} M) :
    ((uliftFunctorSelfIso.{ℓ, v} R).hom.app M).hom x = x.down := rfl

/-- The inverse comparison is the actual native coordinate lifting map. -/
theorem uliftFunctorSelfIso_inv_app_apply (R : Type u) [Ring R]
    (M : ModuleCat.{max ℓ v} R) (x : M) :
    ((uliftFunctorSelfIso.{ℓ, v} R).inv.app M).hom x = ULift.up x := rfl

/-- The contained-level construction retains the existing native zero-lift unit. -/
theorem uliftFunctorSelfIso_zero (R : Type u) [Ring R] :
    uliftFunctorSelfIso.{0, v} R = uliftFunctorZeroIso.{v} R := rfl

/-- Flattening two contained native lifts followed by lowering agrees with both lowerings. -/
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

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Coherence of module universe lifts

The module functor `ModuleCat.uliftFunctor` is compatible with repeated
universe lifting. The flattening isomorphism sends x to
`ULift.up x.down.down` and satisfies the unit and associativity equations.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ModuleCat

universe u v z t s

/-- Flatten the two lifted module carriers into one lift at the maximum
of the two lift universes. -/
def uliftFlattenEquiv.{z₁, t₁, v₁, u₁} (R : Type u₁) [Ring R]
    (M : Type v₁) [AddCommGroup M] [Module R M] :
    ULift.{t₁} (ULift.{z₁} M) ≃ₗ[R] ULift.{max z₁ t₁} M :=
  (ULift.moduleEquiv : ULift.{t₁} (ULift.{z₁} M) ≃ₗ[R] ULift.{z₁} M).trans
    ((ULift.moduleEquiv : ULift.{z₁} M ≃ₗ[R] M).trans
      (ULift.moduleEquiv : ULift.{max z₁ t₁} M ≃ₗ[R] M).symm)

@[simp]
theorem uliftFlattenEquiv_apply (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (x : ULift.{t} (ULift.{z} M)) :
    uliftFlattenEquiv R M x = ULift.up x.down.down := rfl

@[simp]
theorem uliftFlattenEquiv_symm_apply (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (x : ULift.{max z t} M) :
    (uliftFlattenEquiv.{z, t} R M).symm x = ULift.up (ULift.up x.down) := rfl

/-- The composition of two native module lifts is naturally isomorphic to
the native lift at the maximum of their lift universes. -/
def uliftFunctorCompIso.{z₁, t₁, v₁, u₁} (R : Type u₁) [Ring R] :
    uliftFunctor.{z₁, v₁} R ⋙ uliftFunctor.{t₁, max v₁ z₁} R ≅
      uliftFunctor.{max z₁ t₁, v₁} R :=
  NatIso.ofComponents
    (fun M => (uliftFlattenEquiv.{z₁, t₁} R M).toModuleIso) (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

@[simp, nolint simpNF] -- simpNF only sees `Functor.comp_obj` in the coercion's type
theorem uliftFunctorCompIso_hom_app_apply (R : Type u) [Ring R]
    (M : ModuleCat.{v} R) (x : ULift.{t} (ULift.{z} M)) :
    ((uliftFunctorCompIso.{z, t} R).hom.app M).hom x =
      ULift.up x.down.down := rfl

@[simp, nolint simpNF] -- simpNF only sees `Functor.comp_obj` in the coercion's type
theorem uliftFunctorCompIso_inv_app_apply (R : Type u) [Ring R]
    (M : ModuleCat.{v} R) (x : ULift.{max z t} M) :
    ((uliftFunctorCompIso.{z, t} R).inv.app M).hom x =
      ULift.up (ULift.up x.down) := rfl

/-- The native lift with lift universe zero has its concrete module carrier
isomorphism to the identity functor. -/
def uliftFunctorZeroIso.{v₁, u₁} (R : Type u₁) [Ring R] :
    uliftFunctor.{0, v₁} R ≅ 𝟭 (ModuleCat.{v₁} R) :=
  NatIso.ofComponents
    (fun M => (ULift.moduleEquiv : ULift.{0} M ≃ₗ[R] M).toModuleIso) (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

@[simp, nolint simpNF] -- simpNF only sees `Functor.id_obj` in the coercion's type
theorem uliftFunctorZeroIso_hom_app_apply (R : Type u) [Ring R]
    (M : ModuleCat.{v} R) (x : ULift.{0} M) :
    ((uliftFunctorZeroIso R).hom.app M).hom x = x.down := rfl

@[simp, nolint simpNF] -- simpNF only sees `Functor.id_obj` in the coercion's type
theorem uliftFunctorZeroIso_inv_app_apply (R : Type u) [Ring R]
    (M : ModuleCat.{v} R) (x : M) :
    ((uliftFunctorZeroIso R).inv.app M).hom x = ULift.up x := rfl

/-- Flattening a zero inner lift is the native outer lift of coefficient down. -/
theorem uliftFunctorCompIso_zero_left (R : Type u) [Ring R]
    (M : ModuleCat.{v} R) :
    (uliftFunctorCompIso.{0, z} R).hom.app M =
      (uliftFunctor.{z, v} R).map ((uliftFunctorZeroIso R).hom.app M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Flattening a zero outer lift is the zero-lift unit on the inner module. -/
theorem uliftFunctorCompIso_zero_right (R : Type u) [Ring R]
    (M : ModuleCat.{v} R) :
    (uliftFunctorCompIso.{z, 0} R).hom.app M =
      (uliftFunctorZeroIso R).hom.app ((uliftFunctor.{z, v} R).obj M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The two ways of flattening three actual native lifts agree. No category
or module universe is identified by an additional hypothesis. -/
theorem uliftFunctorCompIso_assoc (R : Type u) [Ring R]
    (M : ModuleCat.{v} R) :
    (uliftFunctor.{s, max v z t} R).map
        ((uliftFunctorCompIso.{z, t} R).hom.app M) ≫
      (uliftFunctorCompIso.{max z t, s} R).hom.app M =
    (uliftFunctorCompIso.{t, s} R).hom.app ((uliftFunctor.{z, v} R).obj M) ≫
      (uliftFunctorCompIso.{z, max t s} R).hom.app M := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end ModuleCat

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.LieModuleCat.Basic

/-!
# Restriction of Lie modules

Restriction along a Lie algebra homomorphism `f` keeps the coefficient carrier
and scalar action, with Lie action `[x, m] = [f x, m]`. Lie-module maps induce
maps between the restricted representations. Identity and composite
restrictions are compared by canonical isomorphisms.
-/

@[expose] public section

universe u v v' v'' w w'

open CategoryTheory

namespace LieModuleCat

variable {R : Type u} [CommRing R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]
variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']

/-- Pull back a bundled native representation along a Lie algebra map. -/
@[implicit_reducible]
def restrictObj (f : L →ₗ⁅R⁆ L') (N : LieModuleCat.{w} R L') : LieModuleCat.{w} R L := by
  letI : LieRingModule L N := LieRingModule.compLieHom N f
  letI : LieModule R L N := LieModule.compLieHom N f
  exact of R L N

/-- Restriction keeps the coefficient carrier. -/
theorem restrictObj_carrier (f : L →ₗ⁅R⁆ L') (N : LieModuleCat.{w} R L') :
    (restrictObj f N).carrier = N.carrier := rfl

/-- Restriction uses the target representation at the image of `x`. -/
@[simp]
theorem restrictObj_lie (f : L →ₗ⁅R⁆ L') (N : LieModuleCat.{w} R L')
    (x : L) (m : restrictObj f N) :
    ⁅x, m⁆ = (⁅f x, (m : N)⁆ : N) := rfl

/-- A native coefficient map remains equivariant after restriction. -/
def restrictMap (f : L →ₗ⁅R⁆ L')
    {N : LieModuleCat.{w} R L'} {P : LieModuleCat.{w'} R L'}
    (g : N →ₗ⁅R,L'⁆ P) : restrictObj f N →ₗ⁅R,L⁆ restrictObj f P where
  toLinearMap := g.toLinearMap
  map_lie' := by
    intro x m
    exact g.map_lie (f x) m

@[simp]
theorem restrictMap_apply (f : L →ₗ⁅R⁆ L')
    {N : LieModuleCat.{w} R L'} {P : LieModuleCat.{w'} R L'}
    (g : N →ₗ⁅R,L'⁆ P) (m : restrictObj f N) : restrictMap f g m = g m := rfl

/-- Restriction along a Lie algebra map is a functor on native Lie modules. -/
def restrict (f : L →ₗ⁅R⁆ L') : LieModuleCat.{w} R L' ⥤ LieModuleCat.{w} R L where
  obj := restrictObj f
  map g := restrictMap f g
  map_id N := by
    apply LieModuleHom.ext
    intro m
    rfl
  map_comp g h := by
    apply LieModuleHom.ext
    intro m
    rfl

@[simp]
theorem restrict_obj (f : L →ₗ⁅R⁆ L') (N : LieModuleCat.{w} R L') :
    (restrict f).obj N = restrictObj f N := rfl

theorem restrict_map_apply (f : L →ₗ⁅R⁆ L')
    {N P : LieModuleCat.{w} R L'} (g : N ⟶ P) (m : restrictObj f N) :
    (restrict f).map g m = g m := rfl

instance restrict_additive (f : L →ₗ⁅R⁆ L') : (restrict.{u,v,v',w} f).Additive where
  map_add := by
    intro X Y g h
    apply LieModuleHom.ext
    intro m
    rfl

instance restrict_linear (f : L →ₗ⁅R⁆ L') : (restrict.{u,v,v',w} f).Linear R where
  map_smul := by
    intro X Y g r
    apply LieModuleHom.ext
    intro m
    rfl

/-- Identity restriction is canonically the original representation. -/
def restrictIdIso : restrict (LieHom.id : L →ₗ⁅R⁆ L) ≅ 𝟭 (LieModuleCat.{w} R L) :=
  NatIso.ofComponents
    (fun N =>
      { hom := { toLinearMap := LinearMap.id, map_lie' := by intro x m; rfl }
        inv := { toLinearMap := LinearMap.id, map_lie' := by intro x m; rfl }
        hom_inv_id := by apply LieModuleHom.ext; intro m; rfl
        inv_hom_id := by apply LieModuleHom.ext; intro m; rfl })
    (by intro N P g; apply LieModuleHom.ext; intro m; rfl)

/-- Iterated restriction uses the composite Lie algebra map. -/
def restrictCompIso (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    restrict g ⋙ restrict f ≅ restrict (g.comp f) :=
  NatIso.ofComponents
    (fun N =>
      { hom := { toLinearMap := LinearMap.id, map_lie' := by intro x m; rfl }
        inv := { toLinearMap := LinearMap.id, map_lie' := by intro x m; rfl }
        hom_inv_id := by apply LieModuleHom.ext; intro m; rfl
        inv_hom_id := by apply LieModuleHom.ext; intro m; rfl })
    (by intro N P h; apply LieModuleHom.ext; intro m; rfl)

end LieModuleCat

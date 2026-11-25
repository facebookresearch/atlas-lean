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

public import MathlibExt.Algebra.Category.LieModuleCat.Restriction
public import Mathlib.Algebra.Module.ULift

/-!
# Actual universe lifts of original native Lie coefficients

The carrier is the native `ULift` of the original coefficient module.
Its bracket is the original bracket carried through up/down, so every Lie
and scalar law follows from the original action. Actual up/down Lie maps,
joint Lie-variable maps and height maps preserve those same original values.
No equality between independent coefficient universes is imposed.
-/

@[expose] public section

noncomputable section

universe u v w w' v' z t

open CategoryTheory

namespace LieModuleCat.CoefficientULift

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The original Lie action on the actual lifted original carrier. -/
@[instance_reducible]
def ringModule (M : LieModuleCat.{w} R L) : LieRingModule L (ULift.{z, w} M) where
  bracket x m := ULift.up ⁅x, m.down⁆
  add_lie x y m := by apply ULift.ext; exact add_lie x y m.down
  lie_add x m n := by apply ULift.ext; exact lie_add x m.down n.down
  leibniz_lie x y m := by apply ULift.ext; exact leibniz_lie x y m.down

/-- The original ground scalar compatibility on the actual lifted carrier. -/
theorem lieModule (M : LieModuleCat.{w} R L) :
    letI : LieRingModule L (ULift.{z,w} M) := ringModule.{u,v,w,z} R L M
    LieModule R L (ULift.{z,w} M) := by
  letI : LieRingModule L (ULift.{z,w} M) := ringModule.{u,v,w,z} R L M
  exact
    { smul_lie := by intro r x m; apply ULift.ext; exact smul_lie r x m.down
      lie_smul := by intro r x m; apply ULift.ext; exact lie_smul r x m.down }

attribute [local instance] ringModule lieModule

/-- The actual native Lie coefficient lift. -/
@[implicit_reducible]
def obj (M : LieModuleCat.{w} R L) : LieModuleCat.{max w z} R L := by
  letI : LieRingModule L (ULift.{z,w} M) := ringModule.{u,v,w,z} R L M
  letI : LieModule R L (ULift.{z,w} M) := lieModule.{u,v,w,z} R L M
  exact LieModuleCat.of R L (ULift.{z,w} M)

@[simp]
theorem obj_lie_up (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    ⁅x, (ULift.up m : obj.{u, v, w, z} R L M)⁆ = ULift.up ⁅x, m⁆ := rfl

/-- The original coefficient, as an actual up Lie-module morphism. -/
def up (M : LieModuleCat.{w} R L) : M →ₗ⁅R,L⁆ obj.{u, v, w, z} R L M where
  toLinearMap := (ULift.moduleEquiv : ULift.{z, w} M ≃ₗ[R] M).symm.toLinearMap
  map_lie' := by intro x m; rfl

/-- The actual down Lie-module morphism to the original coefficient carrier. -/
def down (M : LieModuleCat.{w} R L) : obj.{u, v, w, z} R L M →ₗ⁅R,L⁆ M where
  toLinearMap := (ULift.moduleEquiv : ULift.{z, w} M ≃ₗ[R] M).toLinearMap
  map_lie' := by intro x m; rfl

@[simp]
theorem up_apply (M : LieModuleCat.{w} R L) (m : M) : up.{u, v, w, z} R L M m = ULift.up m := rfl

@[simp]
theorem down_apply (M : LieModuleCat.{w} R L) (m : obj.{u, v, w, z} R L M) :
    down.{u, v, w, z} R L M m = m.down := rfl

@[simp]
theorem down_comp_up (M : LieModuleCat.{w} R L) :
    (down.{u, v, w, z} R L M).comp (up.{u, v, w, z} R L M) = LieModuleHom.id := by
  apply LieModuleHom.ext
  intro m
  rfl

@[simp]
theorem up_comp_down (M : LieModuleCat.{w} R L) :
    (up.{u, v, w, z} R L M).comp (down.{u, v, w, z} R L M) = LieModuleHom.id := by
  apply LieModuleHom.ext
  intro m
  rfl

/-- Original coefficient maps carried through the actual native lift. -/
def map {M M' : LieModuleCat.{w} R L} (h : M ⟶ M') :
    obj.{u, v, w, z} R L M ⟶ obj.{u, v, w, z} R L M' :=
  (up.{u, v, w, z} R L M').comp (h.comp (down.{u, v, w, z} R L M))

/-- The coefficient lift is an actual functor on original native Lie modules. -/
def functor : LieModuleCat.{w} R L ⥤ LieModuleCat.{max w z} R L where
  obj := obj.{u, v, w, z} R L
  map := map.{u, v, w, z} R L
  map_id M := by apply LieModuleHom.ext; intro m; rfl
  map_comp h k := by apply LieModuleHom.ext; intro m; rfl

/-- The original native coefficient under a genuinely larger working height. -/
def heightMap (M : LieModuleCat.{w} R L) :
    obj.{u, v, w, z} R L M →ₗ⁅R,L⁆ obj.{u, v, w, max z t} R L M :=
  (up.{u, v, w, max z t} R L M).comp (down.{u, v, w, z} R L M)

@[simp]
theorem heightMap_up (M : LieModuleCat.{w} R L) (m : M) :
    heightMap.{u, v, w, z, t} R L M (ULift.up m) = ULift.up m := rfl

/-- Actual down/up in the two original coefficient heights, including its
computed inverse. This is a linear equivalence across the two actual carriers. -/
def heightLinearEquiv (M : LieModuleCat.{w} R L) :
    obj.{u, v, w, max z t} R L M ≃ₗ[R] obj.{u, v, w, z} R L M :=
  (ULift.moduleEquiv : ULift.{max z t, w} M ≃ₗ[R] M).trans
    (ULift.moduleEquiv : ULift.{z, w} M ≃ₗ[R] M).symm

/-- The actual coefficient down map from the larger working height. -/
def heightDown (M : LieModuleCat.{w} R L) :
    obj.{u, v, w, max z t} R L M →ₗ⁅R,L⁆ obj.{u, v, w, z} R L M :=
  (up.{u, v, w, z} R L M).comp (down.{u, v, w, max z t} R L M)

/-- Actual flattening of two coefficient-carrier lifts, with every Lie and
scalar action retained from the original coefficient carrier. -/
def flattenIso (M : LieModuleCat.{w} R L) :
    obj.{u, v, max w z, t} R L (obj.{u, v, w, z} R L M) ≅
      obj.{u, v, w, max z t} R L M where
  hom :=
    { toLinearMap :=
        { toFun := fun m => ULift.up m.down.down
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_lie' := by intro x m; rfl }
  inv :=
    { toLinearMap :=
        { toFun := fun m => ULift.up (ULift.up m.down)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_lie' := by intro x m; rfl }
  hom_inv_id := by apply LieModuleHom.ext; intro m; rfl
  inv_hom_id := by apply LieModuleHom.ext; intro m; rfl

@[simp]
theorem flattenIso_up (M : LieModuleCat.{w} R L) (m : M) :
    (flattenIso.{u, v, w, z, t} R L M).hom (ULift.up (ULift.up m)) = ULift.up m := rfl

section JointMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L')
  (M : LieModuleCat.{w} R L) (M' : LieModuleCat.{w'} R L')

/-- Joint original Lie/coefficient maps on the two independently sized
actual coefficient lifts. -/
def jointMap (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M') :
    obj.{u, v, w, z} R L M →ₗ⁅R,L⁆
    LieModuleCat.restrictObj f (obj.{u, v', w', z} R L' M') where
  toLinearMap := (ULift.moduleEquiv : ULift.{z, w'} M' ≃ₗ[R] M').symm.toLinearMap.comp
    (h.toLinearMap.comp (ULift.moduleEquiv : ULift.{z, w} M ≃ₗ[R] M).toLinearMap)
  map_lie' := by intro x m; apply ULift.ext; exact h.map_lie x m.down

variable (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

@[simp]
theorem jointMap_up (m : M) :
    jointMap.{u, v, w, w', v', z} R L f M M' h (ULift.up m) = ULift.up (h m) := rfl

/-- The actual joint lift maps commute with the actual native height maps. -/
theorem jointMap_height :
    (jointMap.{u, v, w, w', v', max z t} R L f M M' h).toLinearMap.comp
      (heightMap.{u, v, w, z, t} R L M).toLinearMap =
    (heightMap.{u, v', w', z, t} R L' M').toLinearMap.comp
      (jointMap.{u, v, w, w', v', z} R L f M M' h).toLinearMap := by
  ext m
  rfl

end JointMaps

end LieModuleCat.CoefficientULift

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
# Lie coefficient modules in independent carrier universes

Let R be a commutative ring, L an R-Lie algebra and M a left Lie module,
with independent carrier worlds u, v and w. For an additional height z,
ULift^z M is a Lie module in world max(w,z), with
[x,up(m)] = up([x,m]) and r • up(m) = up(r • m).
The up and down maps are mutually inverse R-linear Lie-module maps.

Lifting coefficient maps defines a functor on LieModuleCat^w(R,L).
Height maps from z to max(z,t) preserve the represented coefficient
value, and the isomorphism ULift^t(ULift^z M) ≅ ULift^max(z,t) M
flattens two lifts.

For a Lie map f : L → L′ and an R-linear map h : M → M′ satisfying
h([x,m]) = [f(x),h(m)], lifting h gives the corresponding joint
Lie/coefficient map. It commutes with the height maps. The worlds of
L, L′, M and M′ may be independent.
-/

@[expose] public section

noncomputable section

universe u v w w' v' z t

open CategoryTheory

namespace LieModuleCat.CoefficientULift

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

/-- For a commutative ring R, an R-Lie algebra L and
M ∈ LieModuleCat^w(R,L), the Lie-ring action on ULift^z M is
[x,m′] = up([x,m′.down]). It inherits additivity and the
Lie-module Jacobi identity from M. -/
@[instance_reducible]
def ringModule (M : LieModuleCat.{w} R L) : LieRingModule L (ULift.{z, w} M) where
  bracket x m := ULift.up ⁅x, m.down⁆
  add_lie x y m := by apply ULift.ext; exact add_lie x y m.down
  lie_add x m n := by apply ULift.ext; exact lie_add x m.down n.down
  leibniz_lie x y m := by apply ULift.ext; exact leibniz_lie x y m.down

/-- For a commutative ring R, an R-Lie algebra L and a Lie
module M, the bracket [x,up(m)] = up([x,m]) on ULift^z M is
R-bilinear. With the lifted R-module structure it makes ULift^z M
an R-Lie module. -/
theorem lieModule (M : LieModuleCat.{w} R L) :
    letI : LieRingModule L (ULift.{z,w} M) := ringModule.{u,v,w,z} R L M
    LieModule R L (ULift.{z,w} M) := by
  letI : LieRingModule L (ULift.{z,w} M) := ringModule.{u,v,w,z} R L M
  exact
    { smul_lie := by intro r x m; apply ULift.ext; exact smul_lie r x m.down
      lie_smul := by intro r x m; apply ULift.ext; exact lie_smul r x m.down }

attribute [local instance] ringModule lieModule

/-- For a commutative ring R, an R-Lie algebra L and
M ∈ LieModuleCat^w(R,L), the lifted coefficient object has carrier
ULift^z M in world max(w,z), pointwise R-action and bracket
[x,up(m)] = up([x,m]). The ring and Lie worlds remain independent. -/
@[implicit_reducible]
def obj (M : LieModuleCat.{w} R L) : LieModuleCat.{max w z} R L := by
  letI : LieRingModule L (ULift.{z,w} M) := ringModule.{u,v,w,z} R L M
  letI : LieModule R L (ULift.{z,w} M) := lieModule.{u,v,w,z} R L M
  exact LieModuleCat.of R L (ULift.{z,w} M)

@[simp]
theorem obj_lie_up (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    ⁅x, (ULift.up m : obj.{u, v, w, z} R L M)⁆ = ULift.up ⁅x, m⁆ := rfl

/-- For a commutative ring R, an R-Lie algebra L and a Lie
module M, the map M → ULift^z M, m ↦ up(m), is R-linear and
intertwines the L-action. It is inverse to the coefficient down map. -/
def up (M : LieModuleCat.{w} R L) : M →ₗ⁅R,L⁆ obj.{u, v, w, z} R L M where
  toLinearMap := (ULift.moduleEquiv : ULift.{z, w} M ≃ₗ[R] M).symm.toLinearMap
  map_lie' := by intro x m; rfl

/-- For a commutative ring R, an R-Lie algebra L and a Lie
module M, the map ULift^z M → M, m′ ↦ m′.down, is R-linear and
intertwines the bracket. It is inverse to the coefficient up map. -/
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

/-- For Lie modules M,M′ over an R-Lie algebra L in the same
carrier world w, a Lie-module morphism h : M → M′ induces
ULift^z M → ULift^z M′ by m′ ↦ up(h(m′.down)).
This map is R-linear and preserves the L-action. -/
def map {M M' : LieModuleCat.{w} R L} (h : M ⟶ M') :
    obj.{u, v, w, z} R L M ⟶ obj.{u, v, w, z} R L M' :=
  (up.{u, v, w, z} R L M').comp (h.comp (down.{u, v, w, z} R L M))

/-- For a commutative ring R and an R-Lie algebra L, coefficient
lifting defines LieModuleCat^w(R,L) → LieModuleCat^max(w,z)(R,L).
It sends M to ULift^z M and sends h to m′ ↦ up(h(m′.down)),
with the inherited R-action and Lie bracket. -/
def functor : LieModuleCat.{w} R L ⥤ LieModuleCat.{max w z} R L where
  obj := obj.{u, v, w, z} R L
  map := map.{u, v, w, z} R L
  map_id M := by apply LieModuleHom.ext; intro m; rfl
  map_comp h k := by apply LieModuleHom.ext; intro m; rfl

/-- For a Lie module M over an R-Lie algebra L, the height map
ULift^z M → ULift^max(z,t) M is m′ ↦ up(m′.down).
It is R-linear and L-equivariant and leaves the underlying
coefficient m ∈ M unchanged. -/
def heightMap (M : LieModuleCat.{w} R L) :
    obj.{u, v, w, z} R L M →ₗ⁅R,L⁆ obj.{u, v, w, max z t} R L M :=
  (up.{u, v, w, max z t} R L M).comp (down.{u, v, w, z} R L M)

@[simp]
theorem heightMap_up (M : LieModuleCat.{w} R L) (m : M) :
    heightMap.{u, v, w, z, t} R L M (ULift.up m) = ULift.up m := rfl

/-- For a Lie module M over an R-Lie algebra L, removing and
reintroducing the coefficient lift gives the R-linear equivalence
ULift^max(z,t) M ≃ₗ[R] ULift^z M.
Its forward map is m′ ↦ up(m′.down), and its inverse uses the
same underlying coefficient at height max(z,t). -/
def heightLinearEquiv (M : LieModuleCat.{w} R L) :
    obj.{u, v, w, max z t} R L M ≃ₗ[R] obj.{u, v, w, z} R L M :=
  (ULift.moduleEquiv : ULift.{max z t, w} M ≃ₗ[R] M).trans
    (ULift.moduleEquiv : ULift.{z, w} M ≃ₗ[R] M).symm

/-- For a Lie module M over an R-Lie algebra L, the map
ULift^max(z,t) M → ULift^z M is m′ ↦ up(m′.down).
It preserves the R-action and Lie bracket and is inverse to
the height map from z to max(z,t). -/
def heightDown (M : LieModuleCat.{w} R L) :
    obj.{u, v, w, max z t} R L M →ₗ⁅R,L⁆ obj.{u, v, w, z} R L M :=
  (up.{u, v, w, z} R L M).comp (down.{u, v, w, max z t} R L M)

/-- For a commutative ring R, an R-Lie algebra L and a Lie
module M, there is a Lie-module isomorphism
ULift^t(ULift^z M) ≅ ULift^max(z,t) M.
It sends up(up(m)) to up(m), with inverse up(m) ↦ up(up(m)),
and preserves both the scalar action and bracket. -/
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

/-- For R-Lie algebras L,L′, a Lie map f : L → L′ and an
R-linear coefficient map h : M → M′ satisfying
h([x,m]) = [f(x),h(m)], the joint lifted map sends
up(m) ∈ ULift^z M to up(h(m)) ∈ ULift^z M′.
The target is restricted along f as an L-module, and both Lie and
coefficient carrier worlds may be independent. -/
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

/-- For a Lie map f : L → L′ and an R-linear coefficient map
h : M → M′ intertwining the Lie actions along f, let h^z and
h^max(z,t) be its coefficient lifts and H_M,H_M′ the height maps.
Then h^max(z,t) ∘ H_M = H_M′ ∘ h^z as R-linear maps from the
height-z M-module to the height-max(z,t) restricted M′-module. -/
theorem jointMap_height :
    (jointMap.{u, v, w, w', v', max z t} R L f M M' h).toLinearMap.comp
      (heightMap.{u, v, w, z, t} R L M).toLinearMap =
    (heightMap.{u, v', w', z, t} R L' M').toLinearMap.comp
      (jointMap.{u, v, w, w', v', z} R L f M M' h).toLinearMap := by
  ext m
  rfl

end JointMaps

end LieModuleCat.CoefficientULift

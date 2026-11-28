/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.LieModuleCat.Basic

/-!
# Restriction of Lie-module representations

Let `R` be a commutative ring and `f : L → L'` an `R`-Lie algebra homomorphism. Restricting an
`L'`-module `N` along `f` retains its additive group and `R`-module structure and defines the
`L`-action by `[x,m] = [f(x),m]`.

Lie-module homomorphisms retain their values after restriction. For a fixed coefficient
universe this gives an additive `R`-linear functor. Identity restriction and iterated
restriction are naturally isomorphic to the identity and composite-map restriction,
respectively. All Lie-algebra and coefficient universes are independent.
-/

@[expose] public section

universe u v v' v'' w w'

open CategoryTheory

namespace LieModuleCat

variable {R : Type u} [CommRing R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]
variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']

/-- The restriction of a Lie-module object.

For `f : L →ₗ⁅R⁆ L'` and an `L'`-module `N`, the restricted module has carrier `N`, the same
`R`-action, and Lie action `[x,m] = [f(x),m]`. -/
@[implicit_reducible]
def restrictObj (f : L →ₗ⁅R⁆ L') (N : LieModuleCat.{w} R L') : LieModuleCat.{w} R L := by
  letI : LieRingModule L N := LieRingModule.compLieHom N f
  letI : LieModule R L N := LieModule.compLieHom N f
  exact of R L N

/-- The carrier of a restricted Lie module.

Restriction along `f : L → L'` retains the coefficient carrier of the given `L'`-module. -/
theorem restrictObj_carrier (f : L →ₗ⁅R⁆ L') (N : LieModuleCat.{w} R L') :
    (restrictObj f N).carrier = N.carrier := rfl

/-- The action formula for Lie-module restriction.

In the restricted representation, the action of `x ∈ L` on `m ∈ N` equals the action of `f(x)
∈ L'` on `m`. -/
@[simp]
theorem restrictObj_lie (f : L →ₗ⁅R⁆ L') (N : LieModuleCat.{w} R L')
    (x : L) (m : restrictObj f N) :
    ⁅x, m⁆ = (⁅f x, (m : N)⁆ : N) := rfl

/-- The restriction of a Lie-module homomorphism.

An `R`-linear `L'`-equivariant map `N → P` is also `L`-equivariant for the actions restricted
along `f`. The source and target coefficient universes may differ. -/
def restrictMap (f : L →ₗ⁅R⁆ L')
    {N : LieModuleCat.{w} R L'} {P : LieModuleCat.{w'} R L'}
    (g : N →ₗ⁅R,L'⁆ P) : restrictObj f N →ₗ⁅R,L⁆ restrictObj f P where
  toLinearMap := g.toLinearMap
  map_lie' := by
    intro x m
    exact g.map_lie (f x) m

/-- The value of a restricted Lie-module homomorphism.

Restricting a coefficient map along `f : L → L'` retains its value at every coefficient
element. -/
@[simp]
theorem restrictMap_apply (f : L →ₗ⁅R⁆ L')
    {N : LieModuleCat.{w} R L'} {P : LieModuleCat.{w'} R L'}
    (g : N →ₗ⁅R,L'⁆ P) (m : restrictObj f N) : restrictMap f g m = g m := rfl

/-- The restriction functor of Lie modules.

For an `R`-Lie algebra map `f : L → L'`, this functor sends `L'`-modules to `L`-modules by the
action `[x,m] = [f(x),m]` and retains coefficient-map values. -/
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

/-- The object formula for Lie-module restriction.

The restriction functor sends an `L'`-module `N` to its carrier with the Lie action pulled
back along `f`. -/
@[simp]
theorem restrict_obj (f : L →ₗ⁅R⁆ L') (N : LieModuleCat.{w} R L') :
    (restrict f).obj N = restrictObj f N := rfl

/-- The morphism formula for the Lie restriction functor.

For `g : N ⟶ P`, the restriction functor satisfies `restrict(f)(g)(m) = g(m)`. -/
theorem restrict_map_apply (f : L →ₗ⁅R⁆ L')
    {N P : LieModuleCat.{w} R L'} (g : N ⟶ P) (m : restrictObj f N) :
    (restrict f).map g m = g m := rfl

/-- Additivity of the Lie restriction functor.

Restriction along a Lie algebra map preserves addition of coefficient homomorphisms. -/
instance restrict_additive (f : L →ₗ⁅R⁆ L') : (restrict.{u,v,v',w} f).Additive where
  map_add := by
    intro X Y g h
    apply LieModuleHom.ext
    intro m
    rfl

/-- Scalar linearity of the Lie restriction functor.

For `r ∈ R`, restriction sends `r • g` to `r` times the restricted coefficient map. -/
instance restrict_linear (f : L →ₗ⁅R⁆ L') : (restrict.{u,v,v',w} f).Linear R where
  map_smul := by
    intro X Y g r
    apply LieModuleHom.ext
    intro m
    rfl

/-- The natural comparison for identity Lie restriction.

Restriction along `id_L` is naturally isomorphic to the identity functor on left `L`-modules.
Both component maps are identity functions on the coefficient carrier. -/
def restrictIdIso : restrict (LieHom.id : L →ₗ⁅R⁆ L) ≅ 𝟭 (LieModuleCat.{w} R L) :=
  NatIso.ofComponents
    (fun N =>
      { hom := { toLinearMap := LinearMap.id, map_lie' := by intro x m; rfl }
        inv := { toLinearMap := LinearMap.id, map_lie' := by intro x m; rfl }
        hom_inv_id := by apply LieModuleHom.ext; intro m; rfl
        inv_hom_id := by apply LieModuleHom.ext; intro m; rfl })
    (by intro N P g; apply LieModuleHom.ext; intro m; rfl)

/-- The natural comparison for composite Lie restriction.

For `f : L → L'` and `g : L' → L''`, restricting first along `g` and then along `f` is
naturally isomorphic to restriction along `g ∘ f`. The component maps are identity functions. -/
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

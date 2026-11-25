/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Bundled modules over a Lie algebra

Objects are left Lie modules and morphisms are Lie-module homomorphisms.
The ring, Lie algebra, and coefficient carrier have independent universes.
Linear maps may have differently sized source and target carriers; fixing the
coefficient universe gives the category used by coefficient chain functors.
-/

@[expose] public section

set_option autoImplicit false

universe w w' v u

open CategoryTheory

/-- The category of native left modules over a fixed Lie algebra. -/
structure LieModuleCat (R : Type u) (L : Type v)
    [CommRing R] [LieRing L] [LieAlgebra R L] where
  /-- The coefficient carrier. -/
  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [moduleStructure : Module R carrier]
  [lieRingModule : LieRingModule L carrier]
  [lieModule : LieModule R L carrier]

attribute [instance] LieModuleCat.addCommGroup LieModuleCat.moduleStructure
  LieModuleCat.lieRingModule LieModuleCat.lieModule

namespace LieModuleCat

variable (R : Type u) (L : Type v)
  [CommRing R] [LieRing L] [LieAlgebra R L]

instance instCoeSort : CoeSort (LieModuleCat.{w} R L) (Type w) := ⟨carrier⟩

/-- Bundle an existing native Lie module without changing its carrier or action. -/
abbrev of (M : Type w) [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] : LieModuleCat.{w} R L where
  carrier := M

/-- Native coefficient maps also make sense between independent carrier universes. -/
abbrev Hom (X : LieModuleCat.{w} R L) (Y : LieModuleCat.{w'} R L) :=
  X →ₗ⁅R,L⁆ Y

instance instCategory : Category (LieModuleCat.{w} R L) where
  Hom := Hom R L
  id _ := LieModuleHom.id
  comp f g := g.comp f
  id_comp f := by
    apply LieModuleHom.ext
    intro m
    rfl
  comp_id f := by
    apply LieModuleHom.ext
    intro m
    rfl
  assoc f g h := by
    apply LieModuleHom.ext
    intro m
    rfl

instance instConcreteCategory : ConcreteCategory (LieModuleCat.{w} R L)
    (fun X Y => X →ₗ⁅R,L⁆ Y) where
  hom f := f
  ofHom f := f
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := rfl
  comp_apply _ _ _ := rfl

/-- Recover the native Lie-module homomorphism underlying a categorical map. -/
abbrev Hom.hom {X Y : LieModuleCat.{w} R L} (f : X ⟶ Y) : X →ₗ⁅R,L⁆ Y :=
  ConcreteCategory.hom f

/-- Regard a native Lie-module homomorphism as a categorical map. -/
abbrev ofHom {X Y : LieModuleCat.{w} R L} (f : X →ₗ⁅R,L⁆ Y) : X ⟶ Y :=
  ConcreteCategory.ofHom f

@[ext]
theorem hom_ext {X Y : LieModuleCat.{w} R L} {f g : X ⟶ Y}
    (h : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext f g h

instance instPreadditive : Preadditive (LieModuleCat.{w} R L) where
  homGroup X Y := inferInstanceAs (AddCommGroup (X →ₗ⁅R,L⁆ Y))
  add_comp X Y Z f g h := by
    apply hom_ext R L
    intro x
    exact (h : Y →ₗ⁅R,L⁆ Z).map_add (f x) (g x)
  comp_add X Y Z f g h := by
    apply hom_ext R L
    intro x
    rfl

instance homModule (X Y : LieModuleCat.{w} R L) : Module R (X ⟶ Y) :=
  inferInstanceAs (Module R (X →ₗ⁅R,L⁆ Y))

instance instLinear : Linear R (LieModuleCat.{w} R L) where
  homModule := homModule R L
  smul_comp X Y Z r f g := by
    apply hom_ext R L
    intro x
    exact (g : Y →ₗ⁅R,L⁆ Z).map_smul r (f x)
  comp_smul X Y Z f r g := by
    apply hom_ext R L
    intro x
    rfl

@[simp]
theorem hom_smul {X Y : LieModuleCat.{w} R L} (r : R) (f : X ⟶ Y) :
    Hom.hom R L (r • f) = r • Hom.hom R L f := rfl

theorem smul_apply {X Y : LieModuleCat.{w} R L} (r : R) (f : X ⟶ Y) (x : X) :
    (r • f) x = r • f x := rfl

/-- Forget only the Lie action, retaining the original coefficient module. -/
def forget : LieModuleCat.{w} R L ⥤ ModuleCat.{w} R where
  obj X := ModuleCat.of R X
  map f := ModuleCat.ofHom f.toLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

@[simp]
theorem forget_obj (X : LieModuleCat.{w} R L) :
    (forget R L).obj X = ModuleCat.of R X := rfl

@[simp]
theorem forget_map {X Y : LieModuleCat.{w} R L} (f : X ⟶ Y) :
    (forget R L).map f = ModuleCat.ofHom f.toLinearMap := rfl

instance forget_faithful : (forget R L).Faithful where
  map_injective h := by
    apply hom_ext R L
    intro x
    exact ConcreteCategory.congr_hom h x

instance forget_additive : (forget R L).Additive where
  map_add {X Y} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance forget_linear : (forget R L).Linear R where
  map_smul {X Y} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

end LieModuleCat

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
# The linear category of Lie modules

Let `R` be a commutative ring and `L` an `R`-Lie algebra. An object is an `R`-module `M` with
an `R`-bilinear Lie action satisfying `[ [x,y], m ] = [x,[y,m]] - [y,[x,m]]`. Morphisms are
`R`-linear maps commuting with this action.

For a fixed coefficient universe these objects form a concrete preadditive `R`-linear
category. The forgetful functor to `R`-modules is faithful, additive, and `R`-linear. The
scalar ring, Lie algebra, and coefficient carrier universes are independent, and Lie-module
homomorphisms can also be formed between differently sized coefficient carriers.
-/

@[expose] public section

set_option autoImplicit false

universe w w' v u

open CategoryTheory

/-- The bundled category of left Lie modules.

For a commutative ring `R` and an `R`-Lie algebra `L`, an object bundles a coefficient
carrier, its additive and `R`-module structures, and a compatible left Lie-module action. -/
structure LieModuleCat (R : Type u) (L : Type v)
    [CommRing R] [LieRing L] [LieAlgebra R L] where
  /-- The carrier of a bundled Lie module.

This is the coefficient type on which the scalar ring and Lie algebra act, in its specified
universe. -/
  carrier : Type w
  /-- The additive group of a bundled Lie module.

  The coefficient carrier is an additive commutative group. -/
  [addCommGroup : AddCommGroup carrier]
  /-- The scalar module structure of a bundled Lie module.

  The coefficient carrier is a module over the commutative scalar ring `R`. -/
  [moduleStructure : Module R carrier]
  /-- The Lie-ring action of a bundled Lie module.

  The coefficient carrier has an additive left action of `L` satisfying the Lie-module Jacobi
  identity. -/
  [lieRingModule : LieRingModule L carrier]
  /-- The scalar compatibility of a bundled Lie action.

  The Lie action on the coefficient carrier is compatible with its `R`-module structure and the
  `R`-Lie algebra structure on `L`. -/
  [lieModule : LieModule R L carrier]

attribute [instance] LieModuleCat.addCommGroup LieModuleCat.moduleStructure
  LieModuleCat.lieRingModule LieModuleCat.lieModule

namespace LieModuleCat

variable (R : Type u) (L : Type v)
  [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The carrier coercion for bundled Lie modules.

A bundled Lie module is regarded as its coefficient carrier type. -/
instance instCoeSort : CoeSort (LieModuleCat.{w} R L) (Type w) := ⟨carrier⟩

/-- The bundled object associated to a Lie module.

For an `R`-module `M` carrying a left `L`-Lie-module structure, this bundles `M` with those
structures and retains its carrier universe. -/
abbrev of (M : Type w) [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] : LieModuleCat.{w} R L where
  carrier := M

/-- Lie-module homomorphisms between independent coefficient carriers.

For bundled modules `X` and `Y`, this is the type of `R`-linear maps `X → Y` commuting with
the `L`-action. The two carrier universes may differ. -/
abbrev Hom (X : LieModuleCat.{w} R L) (Y : LieModuleCat.{w'} R L) :=
  X →ₗ⁅R,L⁆ Y

/-- The category structure on bundled Lie modules.

For a fixed carrier universe, morphisms are Lie-module homomorphisms, identities are identity
maps, and composition is composition of the underlying linear maps. -/
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

/-- The concrete category of Lie modules.

The concrete morphisms are the underlying Lie-module homomorphisms, so their evaluation and
composition agree with evaluation and composition of functions. -/
instance instConcreteCategory : ConcreteCategory (LieModuleCat.{w} R L)
    (fun X Y => X →ₗ⁅R,L⁆ Y) where
  hom f := f
  ofHom f := f
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := rfl
  comp_apply _ _ _ := rfl

/-- The Lie-module homomorphism underlying a categorical map.

For `f : X ⟶ Y`, this is its `R`-linear map commuting with the `L`-action. -/
abbrev Hom.hom {X Y : LieModuleCat.{w} R L} (f : X ⟶ Y) : X →ₗ⁅R,L⁆ Y :=
  ConcreteCategory.hom f

/-- The categorical map associated to a Lie-module homomorphism.

An `R`-linear `L`-equivariant map between bundled modules defines a morphism in the Lie-module
category. -/
abbrev ofHom {X Y : LieModuleCat.{w} R L} (f : X →ₗ⁅R,L⁆ Y) : X ⟶ Y :=
  ConcreteCategory.ofHom f

/-- Extensionality of categorical Lie-module maps.

Two morphisms of bundled Lie modules are equal if they have the same value on every
coefficient element. -/
@[ext]
theorem hom_ext {X Y : LieModuleCat.{w} R L} {f g : X ⟶ Y}
    (h : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext f g h

/-- The preadditive structure on Lie modules.

Each morphism space is an additive commutative group under pointwise addition, and composition
is additive in both variables. -/
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

/-- The scalar module of Lie-module morphisms.

For fixed `X` and `Y`, their morphism space is an `R`-module under pointwise scalar
multiplication. -/
instance homModule (X Y : LieModuleCat.{w} R L) : Module R (X ⟶ Y) :=
  inferInstanceAs (Module R (X →ₗ⁅R,L⁆ Y))

/-- The linear category structure on Lie modules.

The `R`-module structures on morphism spaces make composition `R`-linear in both variables. -/
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

/-- The underlying homomorphism of a scalar multiple.

For `r ∈ R` and `f : X ⟶ Y`, the Lie-module homomorphism underlying `r • f` is `r` times the
homomorphism underlying `f`. -/
@[simp]
theorem hom_smul {X Y : LieModuleCat.{w} R L} (r : R) (f : X ⟶ Y) :
    Hom.hom R L (r • f) = r • Hom.hom R L f := rfl

/-- Evaluation of a scalar multiple of a Lie-module map.

For `r ∈ R`, `f : X ⟶ Y`, and `x ∈ X`, one has `(r • f)(x) = r • f(x)`. -/
theorem smul_apply {X Y : LieModuleCat.{w} R L} (r : R) (f : X ⟶ Y) (x : X) :
    (r • f) x = r • f x := rfl

/-- The forgetful functor from Lie modules to scalar modules.

This functor sends a bundled `L`-module to its underlying `R`-module and a Lie-module map to
its underlying `R`-linear map. -/
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

/-- The scalar module underlying a bundled Lie module.

On an object `X`, the forgetful functor has value the `R`-module with carrier `X`. -/
@[simp]
theorem forget_obj (X : LieModuleCat.{w} R L) :
    (forget R L).obj X = ModuleCat.of R X := rfl

/-- The linear map underlying a forgotten Lie-module morphism.

On `f : X ⟶ Y`, the forgetful functor gives the categorical `R`-module map associated to
`f.toLinearMap`. -/
@[simp]
theorem forget_map {X Y : LieModuleCat.{w} R L} (f : X ⟶ Y) :
    (forget R L).map f = ModuleCat.ofHom f.toLinearMap := rfl

/-- Faithfulness of the Lie-module forgetful functor.

A morphism of Lie modules is determined by its underlying scalar-module map. -/
instance forget_faithful : (forget R L).Faithful where
  map_injective h := by
    apply hom_ext R L
    intro x
    exact ConcreteCategory.congr_hom h x

/-- Additivity of the Lie-module forgetful functor.

The forgetful functor preserves addition of Lie-module morphisms. -/
instance forget_additive : (forget R L).Additive where
  map_add {X Y} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Scalar linearity of the Lie-module forgetful functor.

For `r ∈ R`, the forgetful functor sends `r • f` to `r` times the underlying scalar-module map
of `f`. -/
instance forget_linear : (forget R L).Linear R where
  map_smul {X Y} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

end LieModuleCat

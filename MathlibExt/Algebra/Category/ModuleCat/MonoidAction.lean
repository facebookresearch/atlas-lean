/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Integral monoid-algebra modules from categorical actions

Mathlib already packages a strict action of a monoid `M` on an object of a
category `C` as `Action C M`.  For `C = AddCommGrpCat`, its multiplication law
has the categorical orientation

`(A.ρ (m * n)).asHom = (A.ρ n).asHom ≫ (A.ρ m).asHom`.

On elements this says that `m * n` acts by first applying `n` and then `m`,
which is exactly the usual left-action convention.  This file converts such
an action, and its equivariant maps, to Mathlib's integral representations and
then reuses `Rep.toModuleMonoidAlgebra` to obtain modules over `ℤ[M]`.

The resulting module has the same underlying additive group as the original
action.  `monoidAlgebraModuleForgetIso` records that identification naturally,
and `monoidAlgebraModuleForgetIso_single_smul` gives the characteristic
monomial-action formula.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

noncomputable section

namespace Action

universe u v

variable (M : Type u) [Monoid M]

/-- The integral representation underlying a strict action on an additive
commutative group. -/
def intRepresentation (A : Action AddCommGrpCat.{v} M) :
    Representation ℤ M A.V where
  toFun m := (A.ρ m).asHom.hom.toIntLinearMap
  map_one' := by
    ext x
    change (A.ρ 1).asHom.hom x = x
    simp
  map_mul' m n := by
    ext x
    change (A.ρ (m * n)).asHom.hom x =
      (A.ρ m).asHom.hom ((A.ρ n).asHom.hom x)
    rw [map_mul]
    rfl

@[simp]
theorem intRepresentation_apply (A : Action AddCommGrpCat.{v} M)
    (m : M) (x : A.V) :
    intRepresentation M A m x = (A.ρ m).asHom.hom x :=
  rfl

/-- An equivariant additive map regarded as a morphism of integral
representations. -/
def intRepMap {A B : Action AddCommGrpCat.{v} M} (f : A ⟶ B) :
    Rep.of (intRepresentation M A) ⟶ Rep.of (intRepresentation M B) :=
  Rep.ofHom
    { __ := f.hom.hom.toIntLinearMap
      isIntertwining' := fun m ↦ by
        ext x
        change f.hom.hom ((A.ρ m).asHom.hom x) =
          (B.ρ m).asHom.hom (f.hom.hom x)
        exact CategoryTheory.congr_fun (f.comm m) x }

@[simp]
theorem intRepMap_apply {A B : Action AddCommGrpCat.{v} M}
    (f : A ⟶ B) (x : A.V) :
    (intRepMap M f).hom x = f.hom.hom x :=
  rfl

/-- Strict actions on additive commutative groups, regarded functorially as
integral representations. -/
def intRepFunctor :
    Action AddCommGrpCat.{v} M ⥤ Rep.{v} ℤ M where
  obj A := Rep.of (intRepresentation M A)
  map f := intRepMap M f
  map_id A := by
    apply Rep.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply Rep.hom_ext
    ext x
    rfl

/-- The `ℤ[M]`-module functor associated to strict `M`-actions on additive
commutative groups. -/
def monoidAlgebraModuleFunctor :
    Action AddCommGrpCat.{v} M ⥤ ModuleCat.{v} (MonoidAlgebra ℤ M) :=
  intRepFunctor M ⋙ Rep.toModuleMonoidAlgebra

/-- Passing from an action to its monoid-algebra module preserves addition of
equivariant maps.  In particular, Mathlib's generic `mapHomologicalComplex`
construction applies directly to complexes of strict actions. -/
instance monoidAlgebraModuleFunctor_additive :
    (monoidAlgebraModuleFunctor.{u, v} M).Additive where
  map_add := by
    intro A B f g
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Forgetting the `ℤ[M]`-module produced from an action recovers its
underlying additive commutative group. -/
def monoidAlgebraModuleForgetIso :
    monoidAlgebraModuleFunctor.{u, v} M ⋙
        forget₂ (ModuleCat.{v} (MonoidAlgebra ℤ M)) AddCommGrpCat.{v} ≅
      Action.forget AddCommGrpCat.{v} M :=
  NatIso.ofComponents
    (fun A ↦ (intRepresentation M A).asModuleEquiv.toAddEquiv.toAddCommGrpIso)
    (fun f ↦ by
      ext x
      rfl)

@[simp]
theorem monoidAlgebraModuleForgetIso_hom_apply
    (A : Action AddCommGrpCat.{v} M)
    (x : (monoidAlgebraModuleFunctor M).obj A) :
    (monoidAlgebraModuleForgetIso M).hom.app A x =
      (intRepresentation M A).asModuleEquiv x :=
  rfl

@[simp]
theorem monoidAlgebraModuleForgetIso_inv_apply
    (A : Action AddCommGrpCat.{v} M) (x : A.V) :
    (monoidAlgebraModuleForgetIso M).inv.app A x =
      (intRepresentation M A).asModuleEquiv.symm x :=
  rfl

/-- A monomial of `ℤ[M]` acts as its integer coefficient followed by the
given monoid action. -/
@[simp]
theorem monoidAlgebraModuleForgetIso_single_smul
    (A : Action AddCommGrpCat.{v} M) (m : M) (z : ℤ)
    (x : (monoidAlgebraModuleFunctor M).obj A) :
    (monoidAlgebraModuleForgetIso M).hom.app A
        (MonoidAlgebra.single m z • x) =
      z • (A.ρ m).asHom.hom ((monoidAlgebraModuleForgetIso M).hom.app A x) := by
  change (intRepresentation M A).asModule at x
  change (intRepresentation M A).asModuleEquiv
      (MonoidAlgebra.single m z • x) =
    z • intRepresentation M A m ((intRepresentation M A).asModuleEquiv x)
  rw [Representation.single_smul]
  rfl

/-- The basis monomial attached to `m` acts by the original action of `m`. -/
@[simp]
theorem monoidAlgebraModuleForgetIso_of_smul
    (A : Action AddCommGrpCat.{v} M) (m : M)
    (x : (monoidAlgebraModuleFunctor M).obj A) :
    (monoidAlgebraModuleForgetIso M).hom.app A
        (MonoidAlgebra.of ℤ M m • x) =
      (A.ρ m).asHom.hom ((monoidAlgebraModuleForgetIso M).hom.app A x) := by
  simpa only [MonoidAlgebra.of_apply, one_smul] using
    monoidAlgebraModuleForgetIso_single_smul M A m 1 x

end Action

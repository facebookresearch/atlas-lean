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

public import MathlibExt.LinearAlgebra.TensorProduct.AlgebraTensorHom
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Scalar tensor and restriction for an arbitrary acting algebra

The acting algebra need not be commutative. Native algebra tensor maps and
the native ground-linear tensor Hom universal property give the free-module
functor and its restriction adjunction. A ground basis gives actual free
acting-algebra terms. The exact scalar dictionary on the restricted free
object is compared with its original ground tensor dictionary.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ModuleCat.AlgebraTensor

variable (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]


/-- The original scalar tensor with its actual left acting-algebra action. -/
@[implicit_reducible]
def obj (X : (ModuleCat.{max u v w} R)) : (ModuleCat.{max u v w} A) := ModuleCat.of A (A ⊗[R] X)

/-- The original tensor map has native acting-algebra linearity. -/
@[implicit_reducible]
def map {X Y : (ModuleCat.{max u v w} R)} (f : X ⟶ Y) : obj R A X ⟶ obj R A Y :=
  ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) f.hom)

@[simp]
theorem map_tmul {X Y : (ModuleCat.{max u v w} R)} (f : X ⟶ Y) (a : A) (x : X) :
    (map R A f).hom (a ⊗ₜ[R] x) = a ⊗ₜ[R] f.hom x := rfl

/-- The actual scalar tensor functor into modules over an arbitrary algebra. -/
@[implicit_reducible]
def functor : (ModuleCat.{max u v w} R) ⥤ (ModuleCat.{max u v w} A) where
  obj := obj R A
  map := map R A
  map_id X := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    rfl

instance : (functor.{u, v, w} R A).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change (map R A (f + g)).hom (a ⊗ₜ[R] x) =
      (map R A f).hom (a ⊗ₜ[R] x) + (map R A g).hom (a ⊗ₜ[R] x)
    calc
      _ = a ⊗ₜ[R] (f + g).hom x := map_tmul R A (f + g) a x
      _ = a ⊗ₜ[R] f.hom x + a ⊗ₜ[R] g.hom x := by
        rw [ModuleCat.hom_add, LinearMap.add_apply, TensorProduct.tmul_add]
      _ = _ := congrArg₂ (· + ·) (map_tmul R A f a x).symm (map_tmul R A g a x).symm

/-- The actual unit-evaluation equivalence between the original Hom sets. -/
@[implicit_reducible]
def homEquiv (X : (ModuleCat.{max u v w} R)) (Y : (ModuleCat.{max u v w} A)) :
    (obj R A X ⟶ Y) ≃ (X ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj Y) := by
  let Z := (ModuleCat.restrictScalars (algebraMap R A)).obj Y
  letI : Module R Z := Z.isModule
  letI : Module A Z := inferInstanceAs (Module A Y)
  letI : IsScalarTower R A Z := IsScalarTower.of_compHom R A Y
  exact (ModuleCat.homEquiv (M := obj R A X) (N := Y)).trans
    ((TensorProduct.algebraTensorHomEquiv R A X Z).toEquiv.trans
      (ModuleCat.homEquiv (M := X) (N := Z)).symm)

@[simp]
theorem homEquiv_apply (X : (ModuleCat.{max u v w} R)) (Y : (ModuleCat.{max u v w} A)) (f : obj R A X ⟶ Y) (x : X) :
    (homEquiv R A X Y f).hom x = f.hom ((1 : A) ⊗ₜ[R] x) := rfl

@[simp]
theorem homEquiv_symm_tmul (X : (ModuleCat.{max u v w} R)) (Y : (ModuleCat.{max u v w} A))
    (f : X ⟶ (ModuleCat.restrictScalars (algebraMap R A)).obj Y) (a : A) (x : X) :
    ((homEquiv R A X Y).symm f).hom (a ⊗ₜ[R] x) = a • f.hom x := rfl

/-- The original noncommutative scalar tensor/restriction adjunction. -/
def adjunction : functor.{u, v, w} R A ⊣ ModuleCat.restrictScalars (algebraMap R A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R A
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply ModuleCat.hom_ext
        apply TensorProduct.AlgebraTensorModule.ext
        intro a x
        rw [homEquiv_symm_tmul]
        change a • g.hom (f.hom x) = ((homEquiv R A X Y).symm g).hom (a ⊗ₜ[R] f.hom x)
        rw [homEquiv_symm_tmul]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply ModuleCat.hom_ext
        ext x
        rw [homEquiv_apply]
        rfl }

theorem adjunction_unit_apply (X : (ModuleCat.{max u v w} R)) (x : X) :
    ((adjunction.{u, v, w} R A).unit.app X).hom x = (1 : A) ⊗ₜ[R] x := rfl

theorem adjunction_counit_tmul (Y : (ModuleCat.{max u v w} A)) (a : A)
    (y : (ModuleCat.restrictScalars (algebraMap R A)).obj Y) :
    ((adjunction.{u, v, w} R A).counit.app Y).hom (a ⊗ₜ[R] y) = a • (show Y from y) := rfl

/-- Native scalar restriction recovers the original ground tensor action. -/
def groundEquiv (X : (ModuleCat.{max u v w} R)) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (obj R A X) ≃ₗ[R] A ⊗[R] X :=
  { AddEquiv.refl _ with
    map_smul' := by
      intro r z
      letI : Module R (A ⊗[R] X) := TensorProduct.instModule
      change algebraMap R A r • (show A ⊗[R] X from z) =
        r • (show A ⊗[R] X from z)
      induction z using TensorProduct.induction_on with
      | zero => simp only [smul_zero]
      | add z z' hz hz' => simp only [smul_add, hz, hz']
      | tmul a x =>
          change algebraMap R A r • (a ⊗ₜ[R] x) = r • (a ⊗ₜ[R] x)
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def] }

/-- A ground basis gives a genuine free acting-algebra scalar tensor module. -/
instance obj_moduleFree (X : (ModuleCat.{max u v w} R)) [Module.Free R X] : Module.Free A (obj R A X) :=
  Module.Free.of_basis ((Module.Free.chooseBasis R X).baseChange A)

instance obj_projective (X : (ModuleCat.{max u v w} R)) [Module.Free R X] : Projective (obj R A X) := by
  infer_instance

/-- Freeness of the original algebra and original input gives freeness of
the exact native restricted free object. -/
instance groundObj_moduleFree [Module.Free R A] (X : (ModuleCat.{max u v w} R)) [Module.Free R X] :
    Module.Free R ((ModuleCat.restrictScalars (algebraMap R A)).obj (obj R A X)) := by
  letI : Module.Free R (A ⊗[R] X) := inferInstance
  exact Module.Free.of_equiv (groundEquiv R A X).symm

end ModuleCat.AlgebraTensor

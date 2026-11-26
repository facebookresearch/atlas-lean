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
# Scalar extension and restriction for an associative algebra

Let R be a commutative ring and A an associative unital R-algebra.
At a common module height H = max(u,v,w), scalar extension
F(X) = A ⊗[R] X carries the left A-action
a • (b ⊗ x) = ab ⊗ x. It is left adjoint to restriction G along R → A.

The Hom correspondence sends g : A ⊗[R] X →ₗ[A] Y to
x ↦ g(1 ⊗ x), with inverse h ↦ (a ⊗ x ↦ a • h(x)).
Thus the unit is x ↦ 1 ⊗ x and the counit is a ⊗ y ↦ a • y.
The restricted scalar-extension object has the same ground R-action
as the tensor product A ⊗[R] X.

If X is R-free, F(X) is A-free. If A is also R-free, G(F(X)) is
R-free. These statements allow a noncommutative A and retain the
independent ring worlds u,v and the additional height w.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ModuleCat.AlgebraTensor

variable (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]


/-- For a commutative ring R, an associative unital R-algebra A
and X ∈ ModuleCat^H(R), scalar extension is A ⊗[R] X with
left A-action a • (b ⊗ x) = ab ⊗ x.
It is an A-module at the common height H = max(u,v,w). -/
@[implicit_reducible]
def obj (X : (ModuleCat.{max u v w} R)) : (ModuleCat.{max u v w} A) := ModuleCat.of A (A ⊗[R] X)

/-- For a commutative ring R, an associative unital R-algebra A
and an R-module morphism f : X → Y, the scalar-extension map
A ⊗[R] X → A ⊗[R] Y is id_A ⊗ f.
It is A-linear for the action on the first tensor factor and sends
a ⊗ x to a ⊗ f(x). -/
@[implicit_reducible]
def map {X Y : (ModuleCat.{max u v w} R)} (f : X ⟶ Y) : obj R A X ⟶ obj R A Y :=
  ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) f.hom)

@[simp]
theorem map_tmul {X Y : (ModuleCat.{max u v w} R)} (f : X ⟶ Y) (a : A) (x : X) :
    (map R A f).hom (a ⊗ₜ[R] x) = a ⊗ₜ[R] f.hom x := rfl

/-- For a commutative ring R and an associative unital
R-algebra A, scalar extension defines
ModuleCat^H(R) → ModuleCat^H(A), X ↦ A ⊗[R] X.
It sends a morphism f to id_A ⊗ f, with H = max(u,v,w). -/
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

/-- For a commutative ring R, an associative unital R-algebra A,
an R-module X and an A-module Y at height H, there is a bijection
Hom_A(A ⊗[R] X,Y) ≃ Hom_R(X,GY).
It sends g to x ↦ g(1 ⊗ x), with inverse h sending a ⊗ x to
a • h(x), where G restricts scalars along R → A. -/
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

/-- For a commutative ring R and an associative unital
R-algebra A, the functor F = A ⊗[R] − is left adjoint to
G = restriction along R → A in the module categories at
height H = max(u,v,w). The unit is x ↦ 1 ⊗ x and the counit
is a ⊗ y ↦ a • y. -/
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

/-- For a commutative ring R, an associative unital R-algebra A
and an R-module X, the identity on the tensor carrier gives an
R-linear equivalence G(F(X)) ≃ₗ[R] A ⊗[R] X.
The R-action induced from the left A-action agrees with the
ground tensor-product action. -/
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

/-- For a commutative ring R, an associative unital R-algebra A
and an R-free module X, the module A ⊗[R] X is free over A.
A ground basis of X gives its A-basis after scalar extension;
A need not be free over R for this conclusion. -/
instance obj_moduleFree (X : (ModuleCat.{max u v w} R)) [Module.Free R X] : Module.Free A (obj R A X) :=
  Module.Free.of_basis ((Module.Free.chooseBasis R X).baseChange A)

instance obj_projective (X : (ModuleCat.{max u v w} R)) [Module.Free R X] : Projective (obj R A X) := by
  infer_instance

/-- For a commutative ring R and an associative unital
R-algebra A, if both A and X are free over R, then
G(A ⊗[R] X) is free over R. The restricted scalar action is the
ground action of the tensor product, and the common carrier
height is max(u,v,w). -/
instance groundObj_moduleFree [Module.Free R A] (X : (ModuleCat.{max u v w} R)) [Module.Free R X] :
    Module.Free R ((ModuleCat.restrictScalars (algebraMap R A)).obj (obj R A X)) := by
  letI : Module.Free R (A ⊗[R] X) := inferInstance
  exact Module.Free.of_equiv (groundEquiv R A X).symm

end ModuleCat.AlgebraTensor

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Category.Grp.Monoidal
import MathlibExt.Algebra.Category.Grp.MonoidalPreadditive
import MathlibExt.CategoryTheory.Monoidal.PreservesColimits
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic

/-!
# Concrete checks for the tensor structure on additive groups

The examples use free groups, torsion groups, an empty-index group and
additive matrix groups. They exercise tensor morphisms, universe transport,
unitors, associators, braiding and the closed adjunction on elements.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct Matrix

namespace MathlibExtTest.AddCommGrpMonoidalTransport

private abbrev integers : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ
private abbrev pairs : AddCommGrpCat.{0} := AddCommGrpCat.of (ℤ × ℤ)
private abbrev torsion : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod 4)
private abbrev emptyFree : AddCommGrpCat.{0} := AddCommGrpCat.of (Fin 0 → ℤ)
private abbrev matrices : AddCommGrpCat.{0} :=
  AddCommGrpCat.of (Matrix (Fin 2) (Fin 2) ℤ)

private abbrev first : pairs ⟶ integers :=
  AddCommGrpCat.ofHom (AddMonoidHom.fst ℤ ℤ)

private def twice : integers ⟶ integers :=
  AddCommGrpCat.ofHom
    { toFun := fun z => z + z
      map_zero' := rfl
      map_add' := fun x y => by simp [add_comm, add_left_comm] }

private abbrev coordinateSum : pairs →+ integers :=
  AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ

private def pairProduct : (pairs ⊗ integers : AddCommGrpCat.{0}) ⟶ integers :=
  AddCommGrpCat.ofHom
    ((LinearMap.mul' ℤ ℤ).comp
      (TensorProduct.map
        ((AddMonoidHom.fst ℤ ℤ).toIntLinearMap : (ℤ × ℤ) →ₗ[ℤ] ℤ)
        (LinearMap.id : ℤ →ₗ[ℤ] ℤ))).toAddMonoidHom

private lemma pairProduct_tmul (x : pairs) (y : integers) :
    pairProduct (x ⊗ₜ[ℤ] y) = x.1 * y := by
  change (LinearMap.mul' ℤ ℤ)
    (TensorProduct.map
      ((AddMonoidHom.fst ℤ ℤ).toIntLinearMap : (ℤ × ℤ) →ₗ[ℤ] ℤ)
      (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (x ⊗ₜ[ℤ] y)) = x.1 * y
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mul'_apply]
  rfl

-- These are synthesized from the imported public structure, not hypotheses.
example : MonoidalCategoryStruct AddCommGrpCat.{0} := inferInstance
example : MonoidalCategory AddCommGrpCat.{0} := inferInstance
example : BraidedCategory AddCommGrpCat.{0} := inferInstance
example : SymmetricCategory AddCommGrpCat.{0} := inferInstance
example : MonoidalClosed AddCommGrpCat.{0} := inferInstance
example : MonoidalPreadditive AddCommGrpCat.{0} := inferInstance
example : PreservesColimitsOfSize.{0, 0} (tensorRight torsion) := inferInstance
example : Closed pairs := inferInstance
example : AddCommGrpCat.toModuleCatULiftInt.{0}.functor.Monoidal := inferInstance

example : (pairs ⊗ torsion : AddCommGrpCat.{0}) =
    AddCommGrpCat.of ((ℤ × ℤ) ⊗[ℤ] ZMod 4) := rfl

example : (𝟙_ AddCommGrpCat.{0}) = AddCommGrpCat.of (ULift.{0} ℤ) :=
  AddCommGrpCat.tensorUnit_def

example (x : pairs) (y : integers) :
    (first ⊗ₘ twice) (x ⊗ₜ[ℤ] y) = x.1 ⊗ₜ[ℤ] (y + y) := rfl

example (x : pairs) (y : integers) :
    (pairs ◁ twice) (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℤ] (y + y) :=
  AddCommGrpCat.whiskerLeft_apply pairs twice x y

example (x : pairs) (y : torsion) :
    (first ▷ torsion) (x ⊗ₜ[ℤ] y) = x.1 ⊗ₜ[ℤ] y :=
  AddCommGrpCat.whiskerRight_apply first torsion x y

example (x : pairs) (y : torsion) :
    (β_ pairs torsion).hom (x ⊗ₜ[ℤ] y) = y ⊗ₜ[ℤ] x :=
  AddCommGrpCat.braiding_hom_apply x y

example (x : pairs) (y : torsion) :
    (β_ pairs torsion).inv (y ⊗ₜ[ℤ] x) = x ⊗ₜ[ℤ] y :=
  AddCommGrpCat.braiding_inv_apply x y

example (x : pairs) (y : torsion) :
    ((β_ pairs torsion).hom ≫ (β_ torsion pairs).hom) (x ⊗ₜ[ℤ] y) =
      x ⊗ₜ[ℤ] y := rfl

example (x : pairs) (y : integers) (z : torsion) :
    (α_ pairs integers torsion).hom ((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z) =
      x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] z) :=
  AddCommGrpCat.associator_hom_apply x y z

example (x : pairs) (y : integers) (z : torsion) :
    (α_ pairs integers torsion).inv (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] z)) =
      (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z := rfl

example (a : ℤ) (x : pairs) :
    (λ_ pairs).hom ((ULift.up a) ⊗ₜ[ℤ] x) = a • x :=
  AddCommGrpCat.leftUnitor_hom_apply (ULift.up a) x

example (a : ℤ) (x : pairs) :
    (ρ_ pairs).hom (x ⊗ₜ[ℤ] (ULift.up a)) = a • x :=
  AddCommGrpCat.rightUnitor_hom_apply x (ULift.up a)

example (x : pairs) : (λ_ pairs).inv x = (ULift.up (1 : ℤ)) ⊗ₜ[ℤ] x := rfl
example (x : pairs) : (ρ_ pairs).inv x = x ⊗ₜ[ℤ] (ULift.up (1 : ℤ)) := rfl

-- The triangle on a nontrivial unit scalar uses actual tensor balancing.
example (a : ℤ) (x : pairs) (y : torsion) :
    ((α_ pairs (𝟙_ AddCommGrpCat.{0}) torsion).hom ≫
        pairs ◁ (λ_ torsion).hom)
      ((x ⊗ₜ[ℤ] (ULift.up a)) ⊗ₜ[ℤ] y) =
    ((ρ_ pairs).hom ▷ torsion)
      ((x ⊗ₜ[ℤ] (ULift.up a)) ⊗ₜ[ℤ] y) := by
  change x ⊗ₜ[ℤ] (a • y) = (a • x) ⊗ₜ[ℤ] y
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

-- Both pentagon paths act on the same fourfold tensor representative.
example (x : pairs) (y : integers) (z : torsion) (w : pairs) :
    ((α_ (pairs ⊗ integers : AddCommGrpCat.{0}) torsion pairs).hom ≫
        (α_ pairs integers (torsion ⊗ pairs : AddCommGrpCat.{0})).hom)
      (((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z) ⊗ₜ[ℤ] w) =
    ((α_ pairs integers torsion).hom ▷ pairs ≫
        (α_ pairs (integers ⊗ torsion : AddCommGrpCat.{0}) pairs).hom ≫
        pairs ◁ (α_ integers torsion pairs).hom)
      (((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z) ⊗ₜ[ℤ] w) := rfl

-- The hexagon includes both associativity and the factor-swapping braiding.
example (x : pairs) (y : integers) (z : torsion) :
    ((α_ pairs integers torsion).hom ≫
        (β_ pairs (integers ⊗ torsion : AddCommGrpCat.{0})).hom ≫
        (α_ integers torsion pairs).hom)
      ((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z) =
    ((β_ pairs integers).hom ▷ torsion ≫
        (α_ integers pairs torsion).hom ≫
        integers ◁ (β_ pairs torsion).hom)
      ((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z) := rfl

-- The inducing functor keeps values and uses the lifted integer action.
example (a : ℤ) (x : pairs) :
    (ULift.up a : ULift.{0} ℤ) •
        (show AddCommGrpCat.toModuleCatULiftInt.functor.obj pairs from x) =
      (show AddCommGrpCat.toModuleCatULiftInt.functor.obj pairs from a • x) := rfl

example (x : pairs) :
    (AddCommGrpCat.toModuleCatULiftInt.functor.map first).hom x = x.1 := rfl

example (x : pairs) (y : torsion) :
    (AddCommGrpCat.inducingFunctorData.μIso pairs torsion).hom.hom
        ((show AddCommGrpCat.toModuleCatULiftInt.functor.obj pairs from x) ⊗ₜ[ULift.{0} ℤ]
          (show AddCommGrpCat.toModuleCatULiftInt.functor.obj torsion from y)) =
      (x ⊗ₜ[ℤ] y) := rfl

-- Internal hom, evaluation and currying use concrete additive homomorphisms.
example : (ihom pairs).obj integers = AddCommGrpCat.of (pairs →+ integers) :=
  AddCommGrpCat.ihom_obj pairs integers

example (x : pairs) :
    (ihom.ev pairs).app integers
        (x ⊗ₜ[ℤ] (show (ihom pairs).obj integers from coordinateSum)) =
      x.1 + x.2 := rfl

example (x : pairs) :
    ((show (pairs →+ integers) →+ (pairs →+ integers) from
        ((ihom pairs).map twice).hom) coordinateSum) x =
      (x.1 + x.2) + (x.1 + x.2) := rfl

example (x : pairs) (y : integers) : pairProduct (x ⊗ₜ[ℤ] y) = x.1 * y :=
  pairProduct_tmul x y

example (x : pairs) (y : integers) :
    (show pairs →+ integers from (MonoidalClosed.curry pairProduct) y) x = x.1 * y := by
  change pairProduct (x ⊗ₜ[ℤ] y) = x.1 * y
  exact pairProduct_tmul x y

example : MonoidalClosed.uncurry (MonoidalClosed.curry pairProduct) = pairProduct :=
  MonoidalClosed.uncurry_curry pairProduct

example :
    MonoidalClosed.curry (MonoidalClosed.uncurry (MonoidalClosed.curry pairProduct)) =
      MonoidalClosed.curry pairProduct :=
  MonoidalClosed.curry_uncurry (MonoidalClosed.curry pairProduct)

example (x : pairs) (y : integers) :
    (show pairs →+ (pairs ⊗ integers : AddCommGrpCat.{0}) from
        (ihom.coev pairs).app integers y) x =
      x ⊗ₜ[ℤ] y := rfl

-- Empty-index and torsion groups exercise zero tensors and annihilating scalars.
example (y : torsion) :
    (β_ emptyFree torsion).hom ((0 : emptyFree) ⊗ₜ[ℤ] y) = 0 := by
  rw [TensorProduct.zero_tmul, map_zero]

example (x : pairs) : (first ⊗ₘ (0 : torsion ⟶ torsion)) (x ⊗ₜ[ℤ] (1 : ZMod 4)) = 0 := by
  change x.1 ⊗ₜ[ℤ] (0 : ZMod 4) = 0
  exact TensorProduct.tmul_zero (R := ℤ) (ZMod 4) x.1

example : (λ_ torsion).hom ((ULift.up (4 : ℤ)) ⊗ₜ[ℤ] (1 : ZMod 4)) = 0 := by
  change (4 : ℤ) • (1 : ZMod 4) = 0
  decide

-- An additive matrix group detects that braiding actually reverses factors.
private abbrev e12 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
private abbrev e21 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

private def matrixProduct : matrices ⊗ matrices ⟶ matrices :=
  AddCommGrpCat.ofHom
    (LinearMap.mul' ℤ (Matrix (Fin 2) (Fin 2) ℤ)).toAddMonoidHom

example :
    matrixProduct ((β_ matrices matrices).hom (e12 ⊗ₜ[ℤ] e21)) ≠
      matrixProduct (e12 ⊗ₜ[ℤ] e21) := by
  rw [AddCommGrpCat.braiding_hom_apply]
  change (LinearMap.mul' ℤ (Matrix (Fin 2) (Fin 2) ℤ)) (e21 ⊗ₜ[ℤ] e12) ≠
    (LinearMap.mul' ℤ (Matrix (Fin 2) (Fin 2) ℤ)) (e12 ⊗ₜ[ℤ] e21)
  rw [LinearMap.mul'_apply, LinearMap.mul'_apply]
  decide

-- A higher carrier universe also obtains its structure from the public instances.
private abbrev liftedIntegers : AddCommGrpCat.{1} := AddCommGrpCat.of (ULift.{1} ℤ)

example : MonoidalCategory AddCommGrpCat.{1} := inferInstance
example : BraidedCategory AddCommGrpCat.{1} := inferInstance
example : MonoidalClosed AddCommGrpCat.{1} := inferInstance

example (x y : liftedIntegers) :
    (β_ liftedIntegers liftedIntegers).hom (x ⊗ₜ[ℤ] y) = y ⊗ₜ[ℤ] x :=
  AddCommGrpCat.braiding_hom_apply x y

example (a : ULift.{1} ℤ) (x : liftedIntegers) :
    (λ_ liftedIntegers).hom (a ⊗ₜ[ℤ] x) = a.down • x :=
  AddCommGrpCat.leftUnitor_hom_apply a x

-- This forces the braided transport instance without assuming right preservation.
example {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (X : C) [PreservesColimitsOfSize.{0, 0} (tensorLeft X)] :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) := inferInstance

end MathlibExtTest.AddCommGrpMonoidalTransport

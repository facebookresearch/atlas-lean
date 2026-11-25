/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.SheafInternalExtModels
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Local coefficient multiplication on actual Ext classes

A section r of a ring sheaf gives the actual multiplication endomorphism
on its restriction to the slice site. The coefficient action on Ext is
postcomposition with this endomorphism in the native derived category.
Thus it is fixed before any module-crystal comparison is requested.

References: Stacks Project Tags 01DH/070I; Berthelot--Breen--Messing,
Théorie de Dieudonné cristalline II, the crystalline Ext realization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.SheafLocalExtScalars

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (O : Sheaf J CommRingCat.{max u v})

/-- The actual underlying additive coefficient sheaf. -/
@[instance_reducible] def additiveRingSheaf : Sheaf J AddCommGrpCat.{max u v} :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v} ⋙
    forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})).obj O

/-- Local multiplication is by the actual restriction of the original section r. -/
def scalarMap (P : C) (r : O.obj.obj (op P)) :
    (additiveRingSheaf J O).over P ⟶ (additiveRingSheaf J O).over P where
  hom.app Q := AddCommGrpCat.ofHom {
    toFun := fun x => ((O.obj.map Q.unop.hom.op).hom r) *
      (show O.obj.obj (op Q.unop.left) from x)
    map_zero' := mul_zero _
    map_add' := fun x y => mul_add _ x y }
  hom.naturality {Q Q'} f := by
    apply ConcreteCategory.hom_ext
    intro x
    change O.obj.obj (op Q.unop.left) at x
    change ((O.obj.map Q'.unop.hom.op).hom r) * ((O.obj.map f.unop.left.op).hom x) =
      ((O.obj.map f.unop.left.op).hom (((O.obj.map Q.unop.hom.op).hom r) * x))
    rw [map_mul]
    congr 1
    rw [← RingHom.comp_apply]
    change _ = ((O.obj.map Q.unop.hom.op ≫ O.obj.map f.unop.left.op).hom r)
    rw [← Functor.map_comp, ← op_comp, Over.w]

/-- The local coefficient endomorphism in the native endomorphism ring. -/
def scalarEnd (P : C) (r : O.obj.obj (op P)) : End ((additiveRingSheaf J O).over P) :=
  .of (scalarMap J O P r)

/-- The endomorphism is determined on every object of the actual slice site. -/
theorem scalarEnd_apply (P : C) (r : O.obj.obj (op P)) (Q : Over P)
    (x : O.obj.obj (op Q.left)) :
    ((scalarEnd J O P r).asHom.hom.app (op Q)).hom x = (O.obj.map Q.hom.op).hom r * x := rfl

/-- Actual local scalar multiplication is a unital ring homomorphism. -/
def scalarEndRingHom (P : C) : O.obj.obj (op P) →+* End ((additiveRingSheaf J O).over P) where
  toFun := scalarEnd J O P
  map_zero' := by
    apply End.ext
    apply Sheaf.hom_ext
    ext Q x
    change O.obj.obj (op Q.unop.left) at x
    change (O.obj.map Q.unop.hom.op).hom 0 * x = 0
    rw [map_zero, zero_mul]
  map_one' := by
    apply End.ext
    apply Sheaf.hom_ext
    ext Q x
    change O.obj.obj (op Q.unop.left) at x
    change (O.obj.map Q.unop.hom.op).hom 1 * x = x
    rw [map_one, one_mul]
  map_add' r s := by
    apply End.ext
    apply Sheaf.hom_ext
    ext Q x
    change O.obj.obj (op Q.unop.left) at x
    change (O.obj.map Q.unop.hom.op).hom (r + s) * x =
      (O.obj.map Q.unop.hom.op).hom r * x + (O.obj.map Q.unop.hom.op).hom s * x
    rw [map_add, add_mul]
  map_mul' r s := by
    apply End.ext
    apply Sheaf.hom_ext
    ext Q x
    change O.obj.obj (op Q.unop.left) at x
    change (O.obj.map Q.unop.hom.op).hom (r * s) * x =
      (O.obj.map Q.unop.hom.op).hom r * ((O.obj.map Q.unop.hom.op).hom s * x)
    rw [map_mul, mul_assoc]

/-- Original coefficient multiplication commutes with the actual slice restriction. -/
theorem scalarMap_restrict {P Q : C} (f : P ⟶ Q) (r : O.obj.obj (op Q)) :
    (J.overMapPullback AddCommGrpCat.{max u v} f).map (scalarMap J O Q r) =
      scalarMap J O P ((O.obj.map f.op).hom r) := by
  apply Sheaf.hom_ext
  ext U x
  change O.obj.obj (op U.unop.left) at x
  change ((O.obj.map (U.unop.hom ≫ f).op).hom r) * x =
    ((O.obj.map U.unop.hom.op).hom ((O.obj.map f.op).hom r)) * x
  rw [op_comp, Functor.map_comp]
  rfl

end MathlibExt.CategoryTheory.SheafLocalExtScalars

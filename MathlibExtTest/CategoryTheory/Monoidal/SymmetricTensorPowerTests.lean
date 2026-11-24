/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Monoidal.SymmetricTensorPower
import Mathlib.CategoryTheory.Monoidal.Types.Basic

set_option autoImplicit false

noncomputable section

namespace MathlibExtTest.SymmetricTensorPowerTests

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.MonoidalCategory.SymmetricTensorPower
open scoped MonoidalCategory

universe v' u'

#check SymmetricTensorPower.permutationIso
#check SymmetricTensorPower.permutationIso_refl
#check SymmetricTensorPower.permutationIso_trans
#check SymmetricTensorPower.permutationIso_symm
#check SymmetricTensorPower.permutationIso_hom_naturality
#check SymmetricTensorPower.blockSumIso_natural
#check SymmetricTensorPower.blockSwap

#check @SymmetricTensorPower.permutationIso.{0, 1}
#check @SymmetricTensorPower.permutationIso_refl.{0, 1}
#check @SymmetricTensorPower.permutationIso_trans.{0, 1}
#check @SymmetricTensorPower.permutationIso_symm.{0, 1}
#check @SymmetricTensorPower.permutationIso_hom_naturality.{0, 1}
#check @SymmetricTensorPower.blockSumIso_natural.{0, 1}
#check @SymmetricTensorPower.blockSwap.{0, 1}

#check @SymmetricTensorPower.permutationIso.{1, 2}
#check @SymmetricTensorPower.permutationIso_refl.{1, 2}
#check @SymmetricTensorPower.permutationIso_trans.{1, 2}
#check @SymmetricTensorPower.permutationIso_symm.{1, 2}
#check @SymmetricTensorPower.permutationIso_hom_naturality.{1, 2}
#check @SymmetricTensorPower.blockSumIso_natural.{1, 2}
#check @SymmetricTensorPower.blockSwap.{1, 2}

section Symbolic

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory.{v'} C]
  [SymmetricCategory.{v'} C]
variable (X : C)

example : permutationIso X (Equiv.refl (Fin 0)) = Iso.refl _ :=
  permutationIso_refl X 0

example (e : Equiv.Perm (Fin 1)) : permutationIso X e = Iso.refl _ := by
  rw [Subsingleton.elim e (Equiv.refl (Fin 1)), permutationIso_refl]

example {m n k : ℕ} (e : Fin m ≃ Fin n) (f : Fin n ≃ Fin k) :
    permutationIso X (e.trans f) =
      permutationIso X e ≪≫ permutationIso X f :=
  permutationIso_trans X e f

example {m n : ℕ} (e : Fin m ≃ Fin n) :
    permutationIso X e.symm = (permutationIso X e).symm :=
  permutationIso_symm X e

example {X Y : C} (g : X ⟶ Y) {m n : ℕ} (e : Fin m ≃ Fin n) :
    tensorPowMap g m ≫ (permutationIso Y e).hom =
      (permutationIso X e).hom ≫ tensorPowMap g n :=
  permutationIso_hom_naturality g e

example {X Y : C} (g : X ⟶ Y) :
    tensorPowMap g 2 ≫
        (permutationIso Y (Equiv.swap (0 : Fin 2) 1)).hom =
      (permutationIso X (Equiv.swap (0 : Fin 2) 1)).hom ≫
        tensorPowMap g 2 :=
  permutationIso_hom_naturality g _

example {X Y : C} (g : X ⟶ Y) :
    tensorPowMap g 3 ≫
        (permutationIso Y
          ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))).hom =
      (permutationIso X
          ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))).hom ≫
        tensorPowMap g 3 :=
  permutationIso_hom_naturality g _

example {m m' n n' : ℕ} (e : Fin m ≃ Fin m')
    (f : Fin n ≃ Fin n') :
    tensorIso (permutationIso X e) (permutationIso X f) ≪≫
        (tensorPowObj_add X m' n').symm =
      (tensorPowObj_add X m n).symm ≪≫
        permutationIso X
          (finSumFinEquiv.symm.trans
            ((Equiv.sumCongr e f).trans finSumFinEquiv)) :=
  blockSumIso_natural X e f

example (m n : ℕ) :
    (tensorPowObj_add X m n).symm ≪≫
        permutationIso X
          (finAddFlip : Fin (m + n) ≃ Fin (n + m)) =
      (β_ (tensorPowObj X m) (tensorPowObj X n)) ≪≫
        (tensorPowObj_add X n m).symm :=
  blockSwap X m n

example :
    permutationIso X
        ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)) =
      permutationIso X (Equiv.swap (0 : Fin 3) 1) ≪≫
        permutationIso X (Equiv.swap 1 2) :=
  permutationIso_trans X _ _

end Symbolic

section Concrete

example :
    let a : tensorPowObj Bool 1 := (PUnit.unit, false)
    let b : tensorPowObj Bool 1 := (PUnit.unit, true)
    let z : tensorPowObj Bool 2 :=
      ((tensorPowObj_add Bool 1 1).symm).hom (a, b)
    (permutationIso Bool
      (finAddFlip (m := 1) (n := 1) : Fin 2 ≃ Fin 2)).hom z =
      ((tensorPowObj_add Bool 1 1).symm).hom (b, a) := by
  dsimp only
  have h := congrArg Iso.hom (blockSwap Bool 1 1)
  have h' := congrArg
    (fun q => q ((PUnit.unit, false), (PUnit.unit, true))) h
  change
    (permutationIso Bool
      (finAddFlip (m := 1) (n := 1) : Fin 2 ≃ Fin 2)).hom
        (((tensorPowObj_add Bool 1 1).symm).hom
          ((PUnit.unit, false), (PUnit.unit, true))) =
      ((tensorPowObj_add Bool 1 1).symm).hom
        ((β_ (tensorPowObj Bool 1) (tensorPowObj Bool 1)).hom
          ((PUnit.unit, false), (PUnit.unit, true))) at h'
  have hswap :
      (β_ (tensorPowObj Bool 1) (tensorPowObj Bool 1)).hom
          ((PUnit.unit, false), (PUnit.unit, true)) =
        ((PUnit.unit, true), (PUnit.unit, false)) := rfl
  rw [hswap] at h'
  exact h'

end Concrete

/-! Private generic implementation names remain inaccessible. -/

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MonoidalCategory.SymmetricTensorPower.adjacentSwapIso

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MonoidalCategory.SymmetricTensorPower.oneWayCycleIso

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MonoidalCategory.SymmetricTensorPower.moveZeroIso

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MonoidalCategory.SymmetricTensorPower.moveZeroIso_succ

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MonoidalCategory.SymmetricTensorPower.permutationIsoAux

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MonoidalCategory.SymmetricTensorPower.permutationIsoAux_refl

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MonoidalCategory.SymmetricTensorPower.permutationIsoAux_trans

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MonoidalCategory.SymmetricTensorPower.permutationIso_finCongr

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.MonoidalCategory.SymmetricTensorPower.permutationIsoAux_blockSum

#print axioms SymmetricTensorPower.permutationIso
#print axioms SymmetricTensorPower.permutationIso_refl
#print axioms SymmetricTensorPower.permutationIso_trans
#print axioms SymmetricTensorPower.permutationIso_symm
#print axioms SymmetricTensorPower.permutationIso_hom_naturality
#print axioms SymmetricTensorPower.blockSumIso_natural
#print axioms SymmetricTensorPower.blockSwap

end MathlibExtTest.SymmetricTensorPowerTests

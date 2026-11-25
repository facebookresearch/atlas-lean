/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.ModelCategory.InternalHomSourceWeakEquivalence

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra

namespace MathlibExtTest.InternalHomSourceWeakEquivalence

#check MonoidalClosed.internalHomSourceAdjunction
#check HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant

#check @MonoidalClosed.internalHomSourceAdjunction.{0, 0}
#check @MonoidalClosed.internalHomSourceAdjunction.{1, 1}
#check @MonoidalClosed.internalHomSourceAdjunction.{0, 1}
#check @MonoidalClosed.internalHomSourceAdjunction.{1, 0}

#check @HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant.{0, 0}
#check @HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant.{1, 1}
#check @HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant.{0, 1}
#check @HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant.{1, 0}

section PureAdjunction

variable {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]

variable {A A' : C} {B B' : Cᵒᵖ} (Z : C)

example (k :
    ((MonoidalClosed.internalHom.flip.obj Z).rightOp).obj A ⟶ B) :
    (MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A B k =
      MonoidalClosed.curry
        ((β_ B.unop A).hom ≫ MonoidalClosed.uncurry k.unop) := by
  simp [MonoidalClosed.internalHomSourceAdjunction]
  rfl

example (l : A ⟶ (MonoidalClosed.internalHom.flip.obj Z).obj B) :
    ((MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A B).symm l =
      (MonoidalClosed.curry
        ((β_ A B.unop).hom ≫ MonoidalClosed.uncurry l)).op := by
  simp [MonoidalClosed.internalHomSourceAdjunction]
  rfl

example (k :
    ((MonoidalClosed.internalHom.flip.obj Z).rightOp).obj A ⟶ B) :
    ((MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A B).symm
        ((MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A B k) = k :=
  Equiv.symm_apply_apply _ k

example (l : A ⟶ (MonoidalClosed.internalHom.flip.obj Z).obj B) :
    (MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A B
        (((MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A B).symm l) = l :=
  Equiv.apply_symm_apply _ l

example (a : A' ⟶ A)
    (l : A ⟶ (MonoidalClosed.internalHom.flip.obj Z).obj B) :
    ((MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A' B).symm
        (a ≫ l) =
      (MonoidalClosed.internalHom.flip.obj Z).rightOp.map a ≫
        ((MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A B).symm l :=
  (MonoidalClosed.internalHomSourceAdjunction Z).homEquiv_naturality_left_symm a l

example (k :
    ((MonoidalClosed.internalHom.flip.obj Z).rightOp).obj A ⟶ B)
    (b : B ⟶ B') :
    (MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A B' (k ≫ b) =
      (MonoidalClosed.internalHomSourceAdjunction Z).homEquiv A B k ≫
        (MonoidalClosed.internalHom.flip.obj Z).map b :=
  (MonoidalClosed.internalHomSourceAdjunction Z).homEquiv_naturality_right k b

end PureAdjunction

section WeakInvariance

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HomotopicalAlgebra.IsClosedSymmetricMonoidalModelCategory C]

variable {A B Z : C}

example (i : A ⟶ B) [IsCofibrant A] [IsCofibrant B] [IsFibrant Z]
    (hi : WeakEquivalence i) :
    WeakEquivalence ((MonoidalClosed.pre i).app Z) :=
  HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant i hi

example (e : A ≅ B) [IsCofibrant A] [IsCofibrant B] [IsFibrant Z] :
    WeakEquivalence ((MonoidalClosed.pre e.hom).app Z) :=
  HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant e.hom inferInstance

example (_i : A ⟶ B) [IsCofibrant B] [IsFibrant Z]
    (_hi : WeakEquivalence _i) : True := by
  fail_if_success
    exact HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant _i _hi
  trivial

example (_i : A ⟶ B) [IsCofibrant A] [IsFibrant Z]
    (_hi : WeakEquivalence _i) : True := by
  fail_if_success
    exact HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant _i _hi
  trivial

example (_i : A ⟶ B) [IsCofibrant A] [IsCofibrant B]
    (_hi : WeakEquivalence _i) : True := by
  fail_if_success
    exact HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant _i _hi
  trivial

example (_Z : C) [IsFibrant _Z] : True := by
  fail_if_success
    let _ : Adjunction.IsQuillenAdjunction
        (MonoidalClosed.internalHomSourceAdjunction _Z) := inferInstance
  trivial

end WeakInvariance

section PrivacyAndNonclaims

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.internalHomSource_pullbackHomClauses

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.internalHomSourceAdjunction_isQuillen

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.internalHomSourceQuillenInstance

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.weakEquivalence_pre_app_inverse

#guard_msgs (error, substring := true) in
#check PointedCGWH.weakEquivalence_pre_app_of_cofibrant

#guard_msgs (error, substring := true) in
#check PointedDeltaGenerated.weakEquivalence_pre_app_of_cofibrant

end PrivacyAndNonclaims

#print axioms MonoidalClosed.internalHomSourceAdjunction
#print axioms HomotopicalAlgebra.weakEquivalence_pre_app_of_cofibrant

end MathlibExtTest.InternalHomSourceWeakEquivalence

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

import MathlibExt.CategoryTheory.Operad.OperadObj.UnitLaws

/-!
# Focused O7E unit-laws public-contract packet

Pins the stable downstream-facing contracts for one-color operadic
unit laws: unit data and total isos, the insertion-prefix
composition laws, insertion maps with their factor form, and the
two unit-law equations.
-/

open CategoryTheory
open CategoryTheory.Operad

universe v u

variable {V : Type u} [Category.{v} V] [FiniteTensor V]

-- Unit data and total isos.
noncomputable example (I : FintypeCat) : SubstitutionData :=
  rightUnitData I

noncomputable example (J : FintypeCat) : SubstitutionData :=
  leftUnitData J

noncomputable example (I : FintypeCat) :
    substitutionTotalObj (rightUnitData I) ≅ I :=
  rightUnitTotalIso I

noncomputable example (J : FintypeCat) :
    substitutionTotalObj (leftUnitData J) ≅ J :=
  leftUnitTotalIso J

-- Insertion-prefix composition laws.
example (c : V) (I : FintypeCat) {F G : FiniteFamily V}
    (f : UnitInsertion.rightTensorFamily c I ⟶ F) (g : F ⟶ G) :
    UnitInsertion.rightInsertFromFactor c I f ≫
        (FiniteTensor.tensor (V := V)).map g =
      UnitInsertion.rightInsertFromFactor c I (f ≫ g) :=
  UnitInsertion.rightInsertFromFactor_comp c I f g

example (c : V) {F G : FiniteFamily V}
    (f : UnitInsertion.leftTensorFamily c ⟶ F) (g : F ⟶ G) :
    UnitInsertion.leftInsertFromFactor c f ≫
        (FiniteTensor.tensor (V := V)).map g =
      UnitInsertion.leftInsertFromFactor c (f ≫ g) :=
  UnitInsertion.leftInsertFromFactor_comp c f g

-- Factor homs.
noncomputable example (O : SymmetricCollection V) (η : OperadUnit O)
    (I : FintypeCat) :
    UnitInsertion.rightTensorFamily (O.eval I) I ⟶
      (substitutionFactors O).obj (rightUnitData I) :=
  UnitInsertion.rightFactorHom O η I

noncomputable example (O : SymmetricCollection V) (η : OperadUnit O)
    (J : FintypeCat) :
    UnitInsertion.leftTensorFamily (O.eval J) ⟶
      (substitutionFactors O).obj (leftUnitData J) :=
  UnitInsertion.leftFactorHom O η J

-- Insertion signatures and factor form.
noncomputable example (O : SymmetricCollection V) (η : OperadUnit O)
    (I : FintypeCat) :
    O.eval I ⟶ (substitutionSource O).obj (rightUnitData I) :=
  rightUnitInsert O η I

noncomputable example (O : SymmetricCollection V) (η : OperadUnit O)
    (J : FintypeCat) :
    O.eval J ⟶ (substitutionSource O).obj (leftUnitData J) :=
  leftUnitInsert O η J

example (O : SymmetricCollection V) (η : OperadUnit O)
    (I : FintypeCat) :
    rightUnitInsert O η I =
      UnitInsertion.rightInsertFromFactor (O.eval I) I
        (UnitInsertion.rightFactorHom O η I) :=
  rightUnitInsert_eq_insertFromFactor O η I

example (O : SymmetricCollection V) (η : OperadUnit O)
    (J : FintypeCat) :
    leftUnitInsert O η J =
      UnitInsertion.leftInsertFromFactor (O.eval J)
        (UnitInsertion.leftFactorHom O η J) :=
  leftUnitInsert_eq_insertFromFactor O η J

-- Right unit-law equation.
example (O : SymmetricCollection V) (η : OperadUnit O)
    (γ : OperadSubstitution O) (h : IsRightUnit O η γ)
    (I : FintypeCat) :
    rightUnitInsert O η I ≫ γ.app (rightUnitData I) ≫
        O.relabelIso (rightUnitTotalIso I) =
      𝟙 (O.eval I) :=
  h I

-- Left unit-law equation.
example (O : SymmetricCollection V) (η : OperadUnit O)
    (γ : OperadSubstitution O) (h : IsLeftUnit O η γ)
    (J : FintypeCat) :
    leftUnitInsert O η J ≫ γ.app (leftUnitData J) ≫
        O.relabelIso (leftUnitTotalIso J) =
      𝟙 (O.eval J) :=
  h J

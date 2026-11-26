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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Unit
public import MathlibExt.CategoryTheory.Operad.OperadObj.UnitLaws

/-!
# Unit laws for colored operads

The right- and left-unit insertion maps are built from the unbiased finite-tensor coherence. The
only colored input is the family of unit operations, one at each color.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe w v u

namespace ColoredOperadObj.UnitInsertion

variable {Color : Type u} {V : Type w} [Category.{v} V]

/-- Apply the finite tensor to every member of the right-unit nested family. -/
abbrev rightTensorFamily [FiniteTensor V] (O : ColoredSymmetricCollection Color V)
    (P : ColoredProfile Color) : FiniteFamily V :=
  CategoryTheory.Operad.UnitInsertion.rightTensorFamily (O.obj P) P.inputs

/-- Map the tensor of each right-unit block to its corresponding substitution factor. -/
def rightFactorHom [FiniteTensor V] (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    rightTensorFamily O P ⟶
      (ColoredOperadObj.substitutionFactors O).obj (ColoredSubstitutionData.rightUnit P) where
  equiv := Equiv.refl (Option P.inputs)
  hom := fun o =>
    match o with
    | none =>
        (FiniteTensor.singletonIso (V := V)).hom.app (O.obj P) ≫
          O.map (ColoredSubstitutionData.rightUnitOuterHom P)
    | some i => η (P.inputColor i)

/-- Apply the finite tensor to every member of the left-unit nested family. -/
abbrev leftTensorFamily [FiniteTensor V] (O : ColoredSymmetricCollection Color V)
    (P : ColoredProfile Color) : FiniteFamily V :=
  CategoryTheory.Operad.UnitInsertion.leftTensorFamily (O.obj P)

/-- Map the tensor of each left-unit block to its corresponding substitution factor. -/
def leftFactorHom [FiniteTensor V] (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    leftTensorFamily O P ⟶
      (ColoredOperadObj.substitutionFactors O).obj (ColoredSubstitutionData.leftUnit P) where
  equiv := Equiv.refl (Option PUnit)
  hom := fun o =>
    match o with
    | none =>
        η P.outputColor ≫ O.map (ColoredSubstitutionData.leftUnitOuterHom P)
    | some _ => (FiniteTensor.singletonIso (V := V)).hom.app (O.obj P)

end ColoredOperadObj.UnitInsertion

namespace ColoredOperadObj

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- Insert unit operations at every input of `P`. -/
noncomputable def rightUnitInsert (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    O.obj P ⟶ (substitutionSource O).obj (ColoredSubstitutionData.rightUnit P) :=
  CategoryTheory.Operad.UnitInsertion.rightInsertFromFactor
    (O.obj P) P.inputs (UnitInsertion.rightFactorHom O η P)

/-- Insert `P` into the unique input of the unit at its output color. -/
noncomputable def leftUnitInsert (O : ColoredSymmetricCollection Color V)
    (η : ColoredOperadUnit O) (P : ColoredProfile Color) :
    O.obj P ⟶ (substitutionSource O).obj (ColoredSubstitutionData.leftUnit P) :=
  CategoryTheory.Operad.UnitInsertion.leftInsertFromFactor
    (O.obj P) (UnitInsertion.leftFactorHom O η P)

/-- The right unit law for colored operadic substitution. -/
def IsRightUnit (O : ColoredSymmetricCollection Color V) (η : ColoredOperadUnit O)
    (γ : ColoredOperadSubstitution O) : Prop :=
  ∀ P,
    rightUnitInsert O η P ≫ γ.app (ColoredSubstitutionData.rightUnit P) ≫
      O.map (ColoredSubstitutionData.rightUnitTotalHom P) = 𝟙 (O.obj P)

/-- The left unit law for colored operadic substitution. -/
def IsLeftUnit (O : ColoredSymmetricCollection Color V) (η : ColoredOperadUnit O)
    (γ : ColoredOperadSubstitution O) : Prop :=
  ∀ P,
    leftUnitInsert O η P ≫ γ.app (ColoredSubstitutionData.leftUnit P) ≫
      O.map (ColoredSubstitutionData.leftUnitTotalHom P) = 𝟙 (O.obj P)

end ColoredOperadObj

end CategoryTheory.Operad

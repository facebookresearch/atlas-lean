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

public import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionData

/-!
# Unit substitution shapes for colored operads

This file defines the unary identity profile at a color, the simultaneous right-unit substitution
shape, and the left-unit substitution shape. Their flattened profiles are canonically isomorphic to
the original profile.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe u

namespace ColoredSubstitutionData

variable {Color : Type u}

/-- The unary identity profile at a color, using the ordinary operadic unary arity. -/
def unitProfile (c : Color) : ColoredProfile Color :=
  ColoredProfile.constant arityOne c c

/-- A path of colors induces a canonical map of unary identity profiles. -/
def unitProfileMap {c d : Color} (h : c = d) : unitProfile c ⟶ unitProfile d where
  inputEquiv := Equiv.refl _
  inputColor_eq := fun _ => h
  outputColor_eq := h

@[simp]
theorem unitProfile_mapColors {Color' : Type*} (f : Color → Color') (c : Color) :
    (unitProfile c).mapColors f = unitProfile (f c) :=
  rfl

/-- Substitute a unary identity profile at every input of `P`. -/
def rightUnit (P : ColoredProfile Color) : ColoredSubstitutionData Color where
  outputColor := P.outputColor
  inner :=
    { index := P.inputs
      obj i := unitProfile (P.inputColor i) }

/-- Substitute `P` into the unique input of the unary identity profile at its output color. -/
def leftUnit (P : ColoredProfile Color) : ColoredSubstitutionData Color where
  outputColor := P.outputColor
  inner := (FiniteFamily.singleton (C := ColoredProfile Color)).obj P

@[simp]
theorem rightUnit_mapColors {Color' : Type*} (f : Color → Color')
    (P : ColoredProfile Color) :
    (rightUnit P).mapColors f = rightUnit (P.mapColors f) :=
  rfl

@[simp]
theorem leftUnit_mapColors {Color' : Type*} (f : Color → Color')
    (P : ColoredProfile Color) :
    (leftUnit P).mapColors f = leftUnit (P.mapColors f) :=
  rfl

@[simp]
theorem rightUnit_outerProfile (P : ColoredProfile Color) :
    (rightUnit P).outerProfile = P := by
  cases P
  rfl

@[simp]
theorem leftUnit_outerProfile (P : ColoredProfile Color) :
    (leftUnit P).outerProfile = unitProfile P.outputColor :=
  rfl

/-- The canonical identification of `P` with the outer profile of its right-unit datum. -/
def rightUnitOuterHom (P : ColoredProfile Color) : P ⟶ (rightUnit P).outerProfile where
  inputEquiv := Equiv.refl _
  inputColor_eq := fun _ => rfl
  outputColor_eq := rfl

@[simp]
theorem rightUnitOuterHom_eq_id (P : ColoredProfile Color) :
    rightUnitOuterHom P = 𝟙 P := by
  cases P
  rfl

/-- The canonical identification of the unary unit profile with the outer profile of a left-unit
datum. -/
def leftUnitOuterHom (P : ColoredProfile Color) :
    unitProfile P.outputColor ⟶ (leftUnit P).outerProfile where
  inputEquiv := Equiv.refl _
  inputColor_eq := fun _ => rfl
  outputColor_eq := rfl

@[simp]
theorem leftUnitOuterHom_eq_id (P : ColoredProfile Color) :
    leftUnitOuterHom P = 𝟙 (unitProfile P.outputColor) := by
  cases P
  rfl

/-- The canonical map from the flattened right-unit shape to the original profile. -/
def rightUnitTotalHom (P : ColoredProfile Color) : (rightUnit P).totalProfile ⟶ P where
  inputEquiv := Equiv.sigmaPUnit P.inputs
  inputColor_eq := fun p => by
    cases p.2
    rfl
  outputColor_eq := rfl

/-- The canonical right-unit profile isomorphism. -/
noncomputable def rightUnitTotalIso (P : ColoredProfile Color) :
    (rightUnit P).totalProfile ≅ P :=
  asIso (rightUnitTotalHom P)

@[simp]
theorem rightUnitTotalIso_hom_inputEquiv (P : ColoredProfile Color) :
    (rightUnitTotalIso P).hom.inputEquiv = Equiv.sigmaPUnit P.inputs :=
  rfl

@[simp]
theorem rightUnitTotalHom_mapColors {Color' : Type*} (f : Color → Color')
    (P : ColoredProfile Color) :
    (rightUnitTotalHom P).mapColors f = rightUnitTotalHom (P.mapColors f) :=
  rfl

/-- The canonical map from the flattened left-unit shape to the original profile. -/
def leftUnitTotalHom (P : ColoredProfile Color) : (leftUnit P).totalProfile ⟶ P where
  inputEquiv := (Equiv.sigmaEquivProd PUnit P.inputs).trans (Equiv.punitProd P.inputs)
  inputColor_eq := fun p => by
    cases p.1
    rfl
  outputColor_eq := rfl

/-- The canonical left-unit profile isomorphism. -/
noncomputable def leftUnitTotalIso (P : ColoredProfile Color) :
    (leftUnit P).totalProfile ≅ P :=
  asIso (leftUnitTotalHom P)

@[simp]
theorem leftUnitTotalIso_hom_inputEquiv (P : ColoredProfile Color) :
    (leftUnitTotalIso P).hom.inputEquiv =
      (Equiv.sigmaEquivProd PUnit P.inputs).trans (Equiv.punitProd P.inputs) :=
  rfl

@[simp]
theorem leftUnitTotalHom_mapColors {Color' : Type*} (f : Color → Color')
    (P : ColoredProfile Color) :
    (leftUnitTotalHom P).mapColors f = leftUnitTotalHom (P.mapColors f) :=
  rfl

end ColoredSubstitutionData

end CategoryTheory.Operad

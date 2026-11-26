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

public import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionUnit

/-!
# Associativity shapes for colored substitution

A three-level colored substitution shape is represented recursively as a root output color and a
finite family of two-level branch data. The output colors of the branches are the input colors of
the derived middle profile; they need not coincide with one another. The two possible contractions
have canonically equivalent total profiles by dependent-sum associativity.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe u

/-- Three-level color-matching substitution data. -/
structure ColoredAssocData (Color : Type u) where
  /-- The output color at the root. -/
  outputColor : Color
  /-- The branches below the root, each itself a two-level substitution shape. -/
  branches : FiniteFamily (ColoredSubstitutionData Color)

namespace ColoredAssocData

variable {Color : Type u} {Color' : Type*}

/-- The two-level datum formed from the outer profile of every branch. -/
def middleData (d : ColoredAssocData Color) : ColoredSubstitutionData Color where
  outputColor := d.outputColor
  inner :=
    (FiniteFamily.map ColoredSubstitutionData.outerProfileFunctor).obj d.branches

/-- First contract every branch, then retain those total profiles as the inner family. -/
def outerAfterInnerData (d : ColoredAssocData Color) : ColoredSubstitutionData Color where
  outputColor := d.outputColor
  inner :=
    (FiniteFamily.map ColoredSubstitutionData.totalProfileFunctor).obj d.branches

/-- Flatten the families of innermost profiles before performing the outer substitution. -/
def innerData (d : ColoredAssocData Color) : ColoredSubstitutionData Color where
  outputColor := d.outputColor
  inner := (FiniteFamily.flatten (C := ColoredProfile Color)).obj
    ((FiniteFamily.map ColoredSubstitutionData.innerFamilyFunctor).obj d.branches)

/-- Apply a function to every color in three-level substitution data. -/
def mapColors (f : Color → Color') (d : ColoredAssocData Color) : ColoredAssocData Color' where
  outputColor := f d.outputColor
  branches := (FiniteFamily.map (ColoredSubstitutionData.mapColorsFunctor f)).obj d.branches

@[simp]
theorem mapColors_middleData (f : Color → Color') (d : ColoredAssocData Color) :
    (d.mapColors f).middleData = d.middleData.mapColors f :=
  rfl

@[simp]
theorem mapColors_outerAfterInnerData (f : Color → Color') (d : ColoredAssocData Color) :
    (d.mapColors f).outerAfterInnerData = d.outerAfterInnerData.mapColors f :=
  rfl

@[simp]
theorem mapColors_innerData (f : Color → Color') (d : ColoredAssocData Color) :
    (d.mapColors f).innerData = d.innerData.mapColors f :=
  rfl

/-- The local two-level substitution datum at a root input. -/
abbrev localData (d : ColoredAssocData Color) (i : d.branches.index) :
    ColoredSubstitutionData Color :=
  d.branches.obj i

@[simp]
theorem middleData_inner_obj (d : ColoredAssocData Color) (i : d.branches.index) :
    d.middleData.inner.obj i = (d.localData i).outerProfile :=
  rfl

@[simp]
theorem outerAfterInnerData_inner_obj (d : ColoredAssocData Color)
    (i : d.branches.index) :
    d.outerAfterInnerData.inner.obj i = (d.localData i).totalProfile :=
  rfl

@[simp]
theorem innerData_inner_obj (d : ColoredAssocData Color)
    (i : d.branches.index) (j : (d.localData i).inner.index) :
    d.innerData.inner.obj ⟨i, j⟩ = (d.localData i).inner.obj j :=
  rfl

/-- The outer profile of the flat inner datum is definitionally the total middle profile. -/
@[simp]
theorem innerData_outerProfile (d : ColoredAssocData Color) :
    d.innerData.outerProfile = d.middleData.totalProfile :=
  rfl

/-- The canonical map from the flat total profile to the nested total profile. -/
def totalHom (d : ColoredAssocData Color) :
    d.innerData.totalProfile ⟶ d.outerAfterInnerData.totalProfile where
  inputEquiv := Equiv.sigmaAssoc
    (fun (i : d.branches.index) (j : (d.localData i).inner.index) =>
      ((d.localData i).inner.obj j).inputs)
  inputColor_eq := fun p => by
    rcases p with ⟨⟨i, j⟩, k⟩
    rfl
  outputColor_eq := rfl

/-- The canonical associativity isomorphism between the two total profiles. -/
noncomputable def totalIso (d : ColoredAssocData Color) :
    d.innerData.totalProfile ≅ d.outerAfterInnerData.totalProfile :=
  asIso d.totalHom

@[simp]
theorem totalIso_hom_inputEquiv (d : ColoredAssocData Color) :
    d.totalIso.hom.inputEquiv = Equiv.sigmaAssoc
      (fun (i : d.branches.index) (j : (d.localData i).inner.index) =>
        ((d.localData i).inner.obj j).inputs) :=
  rfl

@[simp]
theorem totalHom_mapColors (f : Color → Color') (d : ColoredAssocData Color) :
    d.totalHom.mapColors f = (d.mapColors f).totalHom :=
  rfl

end ColoredAssocData

end CategoryTheory.Operad

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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Associativity
public import MathlibExt.CategoryTheory.Operad.OperadObj.Associativity

/-!
# Color-blind operadic data

An ordinary symmetric collection can be evaluated on a colored profile by forgetting every color
and retaining only its finite input arity. This module constructs the canonical comparisons for
substitution factors and sources, together with the induced unit and substitution data.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe u v w

namespace ColoredOperadObj.ColorBlind

variable (Color : Type u)
variable {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- Regard an ordinary symmetric collection as a colored collection whose operations ignore all
colors. -/
abbrev collection (O : SymmetricCollection V) : ColoredSymmetricCollection Color V :=
  ColoredProfile.arityFunctor Color ⋙ O

/-- Compare the colored substitution factors with the ordinary factors obtained by forgetting
colors. -/
def factorIso (O : SymmetricCollection V) (d : ColoredSubstitutionData Color) :
    (ColoredOperadObj.substitutionFactors (collection Color O)).obj d ≅
      (Operad.substitutionFactors O).obj d.toSubstitutionData :=
  FiniteFamily.isoOfComponents (Equiv.refl _) (fun
    | none => Iso.refl _
    | some _ => Iso.refl _)

/-- Forward map of `factorIso`. -/
abbrev factorHom (O : SymmetricCollection V) (d : ColoredSubstitutionData Color) :=
  (factorIso Color O d).hom

/-- The color-blind factor comparison, natural in substitution data. -/
def factorNatIso (O : SymmetricCollection V) :
    ColoredOperadObj.substitutionFactors (collection Color O) ≅
      ColoredSubstitutionData.toSubstitutionDataFunctor ⋙ Operad.substitutionFactors O :=
  NatIso.ofComponents (factorIso Color O) (by
    intro d e f
    apply FiniteFamily.Hom_ext
    · rfl
    · intro o
      cases o with
      | none =>
          change HEq
            (O.map (FinBijGroupoid.homOfEquiv f.innerHom.equiv) ≫ 𝟙 _)
            (𝟙 _ ≫ O.map (FinBijGroupoid.homOfEquiv f.innerHom.equiv))
          exact heq_of_eq (by simp)
      | some i =>
          change HEq
            (O.map (FinBijGroupoid.homOfEquiv (f.innerHom.hom i).inputEquiv) ≫ 𝟙 _)
            (𝟙 _ ≫ O.map (FinBijGroupoid.homOfEquiv (f.innerHom.hom i).inputEquiv))
          exact heq_of_eq (by simp))

/-- The induced comparison between colored and ordinary substitution sources. -/
def sourceNatIso (O : SymmetricCollection V) :
    ColoredOperadObj.substitutionSource (collection Color O) ≅
      ColoredSubstitutionData.toSubstitutionDataFunctor ⋙ Operad.substitutionSource O :=
  Functor.isoWhiskerRight (factorNatIso Color O) (FiniteTensor.tensor (V := V))

/-- The source comparison is induced by tensoring the factor-family comparison. -/
@[simp]
theorem sourceNatIso_hom_app (O : SymmetricCollection V)
    (d : ColoredSubstitutionData Color) :
    (sourceNatIso Color O).hom.app d =
      (FiniteTensor.tensor (V := V)).map (factorHom Color O d) :=
  rfl

/-- Repeat an ordinary operadic unit at every color. -/
def unitData (O : SymmetricCollection V) (η : OperadUnit O) :
    ColoredOperadUnit (collection Color O) :=
  fun _ ↦ η

/-- Apply ordinary substitution after forgetting all colors from its substitution shape. -/
def substitutionData (O : SymmetricCollection V) (γ : OperadSubstitution O) :
    ColoredOperadSubstitution (collection Color O) :=
  (sourceNatIso Color O).hom ≫
    Functor.whiskerLeft ColoredSubstitutionData.toSubstitutionDataFunctor γ

/-- Forget every color from a three-level colored substitution shape. -/
def forgetColorsAssocData (d : ColoredAssocData Color) : AssocData where
  outer := d.branches.index
  middle i := (d.localData i).inner.index
  inner p := ((d.localData p.1).inner.obj p.2).inputs

/-- Forgetting colors commutes with the middle substitution datum. -/
@[simp]
theorem forgetColorsAssocData_middleData (d : ColoredAssocData Color) :
    (forgetColorsAssocData Color d).middleData = d.middleData.toSubstitutionData :=
  rfl

/-- Forgetting colors commutes with substituting each inner branch. -/
@[simp]
theorem forgetColorsAssocData_outerAfterInnerData (d : ColoredAssocData Color) :
    (forgetColorsAssocData Color d).outerAfterInnerData =
      d.outerAfterInnerData.toSubstitutionData :=
  rfl

/-- Forgetting colors commutes with flattening the inner substitution data. -/
@[simp]
theorem forgetColorsAssocData_innerData (d : ColoredAssocData Color) :
    (forgetColorsAssocData Color d).innerData = d.innerData.toSubstitutionData :=
  rfl

end ColoredOperadObj.ColorBlind

end CategoryTheory.Operad

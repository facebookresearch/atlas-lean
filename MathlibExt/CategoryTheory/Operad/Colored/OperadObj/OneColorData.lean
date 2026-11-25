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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlindData
public import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionOneColor

/-!
# One-color comparison data for operads

This file compares the raw collection, unit, substitution, and associativity data for ordinary
operads and colored operads with color type `PUnit`. The actual equivalence of operad categories is
constructed only after the unit and associativity routes have been shown compatible.
-/

@[expose] public section

namespace CategoryTheory.Operad.ColoredOperadObj.OneColor

open CategoryTheory

universe w v

variable {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- Regard an ordinary symmetric collection as a one-colored symmetric collection. -/
abbrev colorizeCollection (O : SymmetricCollection V) : ColoredSymmetricCollection PUnit V :=
  ColoredOperadObj.ColorBlind.collection PUnit O

/-- Forget the colors from a one-colored symmetric collection. -/
abbrev uncolorCollection (O : ColoredSymmetricCollection PUnit V) : SymmetricCollection V :=
  ColoredProfile.oneColorFunctor ⋙ O

omit [FiniteTensor V] in
/-- The underlying collection is unchanged by colorizing and then forgetting the unique color. -/
def ordinaryCollectionUnitIso (O : SymmetricCollection V) :
    O ≅ uncolorCollection (colorizeCollection O) :=
  NatIso.ofComponents (fun I ↦ Iso.refl (O.obj I)) (by
    intro I J f
    change O.map f ≫ 𝟙 _ = 𝟙 _ ≫ O.map f
    simp)

omit [FiniteTensor V] in
/-- The ordinary collection round-trip isomorphism has identity forward components. -/
@[simp]
theorem ordinaryCollectionUnitIso_hom_app (O : SymmetricCollection V)
    (I : FinBijGroupoid) :
    (ordinaryCollectionUnitIso O).hom.app I = 𝟙 (O.obj I) := by
  rfl

omit [FiniteTensor V] in
/-- The ordinary collection round-trip isomorphism has identity inverse components. -/
@[simp]
theorem ordinaryCollectionUnitIso_inv_app (O : SymmetricCollection V)
    (I : FinBijGroupoid) :
    (ordinaryCollectionUnitIso O).inv.app I = 𝟙 (O.obj I) := by
  rfl

omit [FiniteTensor V] in
/-- A one-colored collection is recovered after forgetting and restoring its unique color. -/
noncomputable def coloredCollectionCounitIso (O : ColoredSymmetricCollection PUnit V) :
    colorizeCollection (uncolorCollection O) ≅ O :=
  Functor.isoWhiskerRight ColoredProfile.oneColorCounitIso O ≪≫
    Functor.leftUnitor O

omit [FiniteTensor V] in
/-- The forward colored collection counit is induced by the profile counit. -/
@[simp]
theorem coloredCollectionCounitIso_hom_app (O : ColoredSymmetricCollection PUnit V)
    (P : ColoredProfile PUnit) :
    (coloredCollectionCounitIso O).hom.app P =
      O.map (ColoredProfile.oneColorCounitHom P) := by
  simp [coloredCollectionCounitIso]

omit [FiniteTensor V] in
/-- The inverse colored collection counit is induced by the inverse profile counit. -/
@[simp]
theorem coloredCollectionCounitIso_inv_app (O : ColoredSymmetricCollection PUnit V)
    (P : ColoredProfile PUnit) :
    (coloredCollectionCounitIso O).inv.app P =
      O.map (Groupoid.inv (ColoredProfile.oneColorCounitHom P)) := by
  simp [coloredCollectionCounitIso]

/-- Factor-family isomorphism for colorization. -/
abbrev colorizeFactorIso (O : SymmetricCollection V) (d : ColoredSubstitutionData PUnit) :=
  ColoredOperadObj.ColorBlind.factorIso PUnit O d

/-- Identity-component comparison between the colored and ordinary substitution-factor families. -/
abbrev colorizeFactorHom (O : SymmetricCollection V) (d : ColoredSubstitutionData PUnit) :=
  ColoredOperadObj.ColorBlind.factorHom PUnit O d

/-- Natural factor-family comparison for colorization. -/
abbrev colorizeFactorNatIso (O : SymmetricCollection V) :=
  ColoredOperadObj.ColorBlind.factorNatIso PUnit O

/-- Source-functor comparison for colorization. -/
abbrev colorizeSourceNatIso (O : SymmetricCollection V) :=
  ColoredOperadObj.ColorBlind.sourceNatIso PUnit O

@[simp]
theorem colorizeSourceNatIso_hom_app (O : SymmetricCollection V)
    (d : ColoredSubstitutionData PUnit) :
    (colorizeSourceNatIso O).hom.app d =
      (FiniteTensor.tensor (V := V)).map (colorizeFactorHom O d) :=
  rfl

/-- Factor-family isomorphism for forgetting one color. -/
def uncolorFactorIso (O : ColoredSymmetricCollection PUnit V) (d : SubstitutionData) :
    (Operad.substitutionFactors (uncolorCollection O)).obj d ≅
      (substitutionFactors O).obj (ColoredSubstitutionData.oneColorFunctor.obj d) :=
  FiniteFamily.isoOfComponents (Equiv.refl _) (fun
    | none => Iso.refl _
    | some _ => Iso.refl _)

/-- Identity-component comparison between the ordinary and colored factor families after forgetting
a one-colored collection. -/
abbrev uncolorFactorHom (O : ColoredSymmetricCollection PUnit V) (d : SubstitutionData) :=
  (uncolorFactorIso O d).hom

/-- Natural factor-family comparison for forgetting one color. -/
def uncolorFactorNatIso (O : ColoredSymmetricCollection PUnit V) :
    Operad.substitutionFactors (uncolorCollection O) ≅
      ColoredSubstitutionData.oneColorFunctor ⋙ substitutionFactors O :=
  NatIso.ofComponents (uncolorFactorIso O) (by
    intro d e f
    apply FiniteFamily.Hom_ext
    · rfl
    · intro o
      cases o with
      | none =>
          change HEq
            (O.map (ColoredProfile.oneColorFunctor.map
              (FinBijGroupoid.homOfEquiv f.equiv)) ≫ 𝟙 _)
            (𝟙 _ ≫ O.map
              (ColoredSubstitutionData.outerProfileMap
                (ColoredSubstitutionData.oneColorFunctor.map f)))
          apply heq_of_eq
          rw [Category.comp_id, Category.id_comp]
          congr 1
      | some i =>
          change HEq
            (O.map (ColoredProfile.oneColorFunctor.map (f.hom i)) ≫ 𝟙 _)
            (𝟙 _ ≫ O.map
              ((ColoredSubstitutionData.oneColorFunctor.map f).innerHom.hom i))
          apply heq_of_eq
          rw [Category.comp_id, Category.id_comp]
          rfl)

/-- Source-functor comparison for forgetting one color. -/
def uncolorSourceNatIso (O : ColoredSymmetricCollection PUnit V) :
    Operad.substitutionSource (uncolorCollection O) ≅
      ColoredSubstitutionData.oneColorFunctor ⋙ substitutionSource O :=
  Functor.isoWhiskerRight (uncolorFactorNatIso O) (FiniteTensor.tensor (V := V))

@[simp]
theorem uncolorSourceNatIso_hom_app (O : ColoredSymmetricCollection PUnit V)
    (d : SubstitutionData) :
    (uncolorSourceNatIso O).hom.app d =
      (FiniteTensor.tensor (V := V)).map (uncolorFactorHom O d) :=
  rfl

/-- Colorize an ordinary operadic unit. -/
abbrev colorizeUnit (O : SymmetricCollection V) (η : OperadUnit O) :
    ColoredOperadUnit (colorizeCollection O) :=
  ColoredOperadObj.ColorBlind.unitData PUnit O η

/-- Colorize an ordinary substitution operation. -/
abbrev colorizeSubst (O : SymmetricCollection V) (γ : OperadSubstitution O) :
    ColoredOperadSubstitution (colorizeCollection O) :=
  ColoredOperadObj.ColorBlind.substitutionData PUnit O γ

@[simp]
theorem colorizeSubst_app (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredSubstitutionData PUnit) :
    (colorizeSubst O γ).app d =
      (colorizeSourceNatIso O).hom.app d ≫
        γ.app (ColoredSubstitutionData.forgetOneColorFunctor.obj d) :=
  rfl

/-- Forget the colors from a one-colored operadic unit. -/
def uncolorUnit (O : ColoredSymmetricCollection PUnit V) (η : ColoredOperadUnit O) :
    OperadUnit (uncolorCollection O) :=
  η PUnit.unit

/-- Forget the colors from a one-colored substitution operation. -/
def uncolorSubst (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) : OperadSubstitution (uncolorCollection O) :=
  (uncolorSourceNatIso O).hom ≫
    Functor.whiskerLeft ColoredSubstitutionData.oneColorFunctor γ

@[simp]
theorem uncolorSubst_app (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : SubstitutionData) :
    (uncolorSubst O γ).app d =
      (uncolorSourceNatIso O).hom.app d ≫
        γ.app (ColoredSubstitutionData.oneColorFunctor.obj d) :=
  rfl

@[simp]
theorem oneColorFunctor_obj_rightUnitData (I : FintypeCat) :
    ColoredSubstitutionData.oneColorFunctor.obj (rightUnitData I) =
      ColoredSubstitutionData.rightUnit (ColoredProfile.oneColorFunctor.obj ⟨I⟩) :=
  rfl

@[simp]
theorem oneColorFunctor_obj_leftUnitData (I : FintypeCat) :
    ColoredSubstitutionData.oneColorFunctor.obj (leftUnitData I) =
      ColoredSubstitutionData.leftUnit (ColoredProfile.oneColorFunctor.obj ⟨I⟩) :=
  rfl

@[simp]
theorem forgetOneColorFunctor_obj_rightUnit (P : ColoredProfile PUnit) :
    ColoredSubstitutionData.forgetOneColorFunctor.obj (ColoredSubstitutionData.rightUnit P) =
      rightUnitData P.inputs :=
  rfl

@[simp]
theorem forgetOneColorFunctor_obj_leftUnit (P : ColoredProfile PUnit) :
    ColoredSubstitutionData.forgetOneColorFunctor.obj (ColoredSubstitutionData.leftUnit P) =
      leftUnitData P.inputs :=
  rfl

/-- Colorize ordinary three-level associativity data. -/
def colorizeAssocData (d : AssocData) : ColoredAssocData PUnit where
  outputColor := PUnit.unit
  branches :=
    { index := d.outer
      obj i := ColoredSubstitutionData.oneColorFunctor.obj (d.localData i) }

@[simp]
theorem colorizeAssocData_middleData (d : AssocData) :
    (colorizeAssocData d).middleData =
      ColoredSubstitutionData.oneColorFunctor.obj d.middleData :=
  rfl

@[simp]
theorem colorizeAssocData_outerAfterInnerData (d : AssocData) :
    (colorizeAssocData d).outerAfterInnerData =
      ColoredSubstitutionData.oneColorFunctor.obj d.outerAfterInnerData :=
  rfl

@[simp]
theorem colorizeAssocData_innerData (d : AssocData) :
    (colorizeAssocData d).innerData =
      ColoredSubstitutionData.oneColorFunctor.obj d.innerData :=
  rfl

/-- Forget all colors from one-colored three-level associativity data. -/
abbrev uncolorAssocData (d : ColoredAssocData PUnit) : AssocData :=
  ColoredOperadObj.ColorBlind.forgetColorsAssocData PUnit d

@[simp]
theorem uncolorAssocData_middleData (d : ColoredAssocData PUnit) :
    (uncolorAssocData d).middleData =
      ColoredSubstitutionData.forgetOneColorFunctor.obj d.middleData :=
  rfl

@[simp]
theorem uncolorAssocData_outerAfterInnerData (d : ColoredAssocData PUnit) :
    (uncolorAssocData d).outerAfterInnerData =
      ColoredSubstitutionData.forgetOneColorFunctor.obj d.outerAfterInnerData :=
  rfl

@[simp]
theorem uncolorAssocData_innerData (d : ColoredAssocData PUnit) :
    (uncolorAssocData d).innerData =
      ColoredSubstitutionData.forgetOneColorFunctor.obj d.innerData :=
  rfl

end CategoryTheory.Operad.ColoredOperadObj.OneColor

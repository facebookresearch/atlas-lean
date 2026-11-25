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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlindUnit
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.OneColorData

/-!
# One-color compatibility of operadic units

The colored right- and left-unit insertion routes agree with the ordinary routes after applying the
canonical source comparison. These theorems are the unit-law regression tests for the one-color
bridge.
-/

@[expose] public section

namespace CategoryTheory.Operad.ColoredOperadObj.OneColor

open CategoryTheory

universe w v

variable {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- The outer-profile map for a colorized right-unit shape is the identity. -/
@[simp]
theorem rightUnitOuterHom_oneColor (I : FintypeCat) :
    ColoredSubstitutionData.rightUnitOuterHom
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) =
      𝟙 (ColoredProfile.oneColorFunctor.obj ⟨I⟩) := by
  apply ColoredProfile.Hom.ext
  rfl

/-- The outer-profile map for a colorized left-unit shape is the identity. -/
@[simp]
theorem leftUnitOuterHom_oneColor (I : FintypeCat) :
    ColoredSubstitutionData.leftUnitOuterHom
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) =
      𝟙 (ColoredSubstitutionData.unitProfile PUnit.unit) := by
  apply ColoredProfile.Hom.ext
  rfl


/-- The colorized right-unit insertion followed by the source comparison is the ordinary
right-unit insertion. -/
theorem colorize_rightUnitInsert (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile PUnit) :
    ColoredOperadObj.rightUnitInsert (colorizeCollection O) (colorizeUnit O η) P ≫
        (colorizeSourceNatIso O).hom.app (ColoredSubstitutionData.rightUnit P) =
      CategoryTheory.Operad.rightUnitInsert O η P.inputs :=
  ColoredOperadObj.ColorBlind.rightUnitInsert_compat PUnit O η P

/-- The colorized left-unit insertion followed by the source comparison is the ordinary left-unit
insertion. -/
theorem colorize_leftUnitInsert (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile PUnit) :
    ColoredOperadObj.leftUnitInsert (colorizeCollection O) (colorizeUnit O η) P ≫
        (colorizeSourceNatIso O).hom.app (ColoredSubstitutionData.leftUnit P) =
      CategoryTheory.Operad.leftUnitInsert O η P.inputs :=
  ColoredOperadObj.ColorBlind.leftUnitInsert_compat PUnit O η P

private theorem uncolorRightFactor_comp (O : ColoredSymmetricCollection PUnit V)
    (η : ColoredOperadUnit O) (I : FintypeCat) :
    CategoryTheory.Operad.UnitInsertion.rightFactorHom
          (uncolorCollection O) (uncolorUnit O η) I ≫
        uncolorFactorHom O (rightUnitData I) =
      ColoredOperadObj.UnitInsertion.rightFactorHom O η
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) := by
  let lhs := CategoryTheory.Operad.UnitInsertion.rightFactorHom
      (uncolorCollection O) (uncolorUnit O η) I ≫
    uncolorFactorHom O (rightUnitData I)
  let rhs := ColoredOperadObj.UnitInsertion.rightFactorHom O η
    (ColoredProfile.oneColorFunctor.obj ⟨I⟩)
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        let a := (FiniteTensor.singletonIso (V := V)).hom.app
          (O.obj (ColoredProfile.oneColorFunctor.obj ⟨I⟩))
        have hMap : O.map (ColoredSubstitutionData.rightUnitOuterHom
            (ColoredProfile.oneColorFunctor.obj ⟨I⟩)) = 𝟙 _ := by
          rw [rightUnitOuterHom_oneColor]
          exact O.map_id _
        have hLeft : HEq (lhs.hom none) a := by
          with_unfolding_all
            exact heq_of_eq ((show lhs.hom none = a ≫ 𝟙 _ from rfl).trans
              (Category.comp_id _))
        have hRight : HEq a (rhs.hom none) := by
          have h0 : HEq (rhs.hom none)
              (a ≫ O.map (ColoredSubstitutionData.rightUnitOuterHom
                (ColoredProfile.oneColorFunctor.obj ⟨I⟩))) := by
            with_unfolding_all exact heq_of_eq rfl
          have h1 : HEq
              (a ≫ O.map (ColoredSubstitutionData.rightUnitOuterHom
                (ColoredProfile.oneColorFunctor.obj ⟨I⟩))) (a ≫ 𝟙 _) :=
            heq_of_eq (congrArg (fun t => a ≫ t) hMap)
          have h2 : HEq (a ≫ 𝟙 _) a := heq_of_eq (Category.comp_id _)
          exact ((h0.trans h1).trans h2).symm
        exact hLeft.trans hRight
    | some i =>
        have hLeft : HEq (lhs.hom (some i)) (η PUnit.unit) := by
          with_unfolding_all
            exact heq_of_eq ((show lhs.hom (some i) = η PUnit.unit ≫ 𝟙 _ from rfl).trans
              (Category.comp_id _))
        have hRight : HEq (η PUnit.unit) (rhs.hom (some i)) := by
          with_unfolding_all exact heq_of_eq rfl
        exact hLeft.trans hRight

private theorem uncolorLeftFactor_comp (O : ColoredSymmetricCollection PUnit V)
    (η : ColoredOperadUnit O) (I : FintypeCat) :
    CategoryTheory.Operad.UnitInsertion.leftFactorHom
          (uncolorCollection O) (uncolorUnit O η) I ≫
        uncolorFactorHom O (leftUnitData I) =
      ColoredOperadObj.UnitInsertion.leftFactorHom O η
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) := by
  let lhs := CategoryTheory.Operad.UnitInsertion.leftFactorHom
      (uncolorCollection O) (uncolorUnit O η) I ≫
    uncolorFactorHom O (leftUnitData I)
  let rhs := ColoredOperadObj.UnitInsertion.leftFactorHom O η
    (ColoredProfile.oneColorFunctor.obj ⟨I⟩)
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        have hMap : O.map (ColoredSubstitutionData.leftUnitOuterHom
            (ColoredProfile.oneColorFunctor.obj ⟨I⟩)) = 𝟙 _ := by
          rw [leftUnitOuterHom_oneColor]
          exact O.map_id _
        have hLeft : HEq (lhs.hom none) (η PUnit.unit) := by
          with_unfolding_all
            exact heq_of_eq ((show lhs.hom none = η PUnit.unit ≫ 𝟙 _ from rfl).trans
              (Category.comp_id _))
        have hRight : HEq (η PUnit.unit) (rhs.hom none) := by
          have h0 : HEq (rhs.hom none)
              (η PUnit.unit ≫ O.map (ColoredSubstitutionData.leftUnitOuterHom
                (ColoredProfile.oneColorFunctor.obj ⟨I⟩))) := by
            with_unfolding_all exact heq_of_eq rfl
          have h1 : HEq
              (η PUnit.unit ≫ O.map (ColoredSubstitutionData.leftUnitOuterHom
                (ColoredProfile.oneColorFunctor.obj ⟨I⟩))) (η PUnit.unit ≫ 𝟙 _) :=
            heq_of_eq (congrArg (fun t => η PUnit.unit ≫ t) hMap)
          have h2 : HEq (η PUnit.unit ≫ 𝟙 _) (η PUnit.unit) :=
            heq_of_eq (Category.comp_id _)
          exact ((h0.trans h1).trans h2).symm
        exact hLeft.trans hRight
    | some i =>
        let a := (FiniteTensor.singletonIso (V := V)).hom.app
          (O.obj (ColoredProfile.oneColorFunctor.obj ⟨I⟩))
        have hLeft : HEq (lhs.hom (some i)) a := by
          with_unfolding_all
            exact heq_of_eq ((show lhs.hom (some i) = a ≫ 𝟙 _ from rfl).trans
              (Category.comp_id _))
        have hRight : HEq a (rhs.hom (some i)) := by
          with_unfolding_all exact heq_of_eq rfl
        exact hLeft.trans hRight

/-- The ordinary right-unit insertion followed by the source comparison is the one-colored
right-unit insertion. -/
theorem uncolor_rightUnitInsert (O : ColoredSymmetricCollection PUnit V)
    (η : ColoredOperadUnit O) (I : FintypeCat) :
    CategoryTheory.Operad.rightUnitInsert (uncolorCollection O) (uncolorUnit O η) I ≫
        (uncolorSourceNatIso O).hom.app (rightUnitData I) =
      ColoredOperadObj.rightUnitInsert O η
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) := by
  rw [rightUnitInsert_eq_insertFromFactor]
  rw [uncolorSourceNatIso_hom_app]
  change
    CategoryTheory.Operad.UnitInsertion.rightInsertFromFactor
          ((uncolorCollection O).eval I) I
          (CategoryTheory.Operad.UnitInsertion.rightFactorHom
            (uncolorCollection O) (uncolorUnit O η) I) ≫
        (FiniteTensor.tensor (V := V)).map (uncolorFactorHom O (rightUnitData I)) =
      CategoryTheory.Operad.UnitInsertion.rightInsertFromFactor
        (O.obj (ColoredProfile.oneColorFunctor.obj ⟨I⟩)) I
        (ColoredOperadObj.UnitInsertion.rightFactorHom O η
          (ColoredProfile.oneColorFunctor.obj ⟨I⟩))
  calc
    _ = CategoryTheory.Operad.UnitInsertion.rightInsertFromFactor
        ((uncolorCollection O).eval I) I
        (CategoryTheory.Operad.UnitInsertion.rightFactorHom
            (uncolorCollection O) (uncolorUnit O η) I ≫
          uncolorFactorHom O (rightUnitData I)) :=
      CategoryTheory.Operad.UnitInsertion.rightInsertFromFactor_comp _ _ _ _
    _ = _ := by
      rw [uncolorRightFactor_comp]
      with_unfolding_all rfl

/-- The ordinary left-unit insertion followed by the source comparison is the one-colored
left-unit insertion. -/
theorem uncolor_leftUnitInsert (O : ColoredSymmetricCollection PUnit V)
    (η : ColoredOperadUnit O) (I : FintypeCat) :
    CategoryTheory.Operad.leftUnitInsert (uncolorCollection O) (uncolorUnit O η) I ≫
        (uncolorSourceNatIso O).hom.app (leftUnitData I) =
      ColoredOperadObj.leftUnitInsert O η
        (ColoredProfile.oneColorFunctor.obj ⟨I⟩) := by
  rw [leftUnitInsert_eq_insertFromFactor]
  rw [uncolorSourceNatIso_hom_app]
  change
    CategoryTheory.Operad.UnitInsertion.leftInsertFromFactor
          ((uncolorCollection O).eval I)
          (CategoryTheory.Operad.UnitInsertion.leftFactorHom
            (uncolorCollection O) (uncolorUnit O η) I) ≫
        (FiniteTensor.tensor (V := V)).map (uncolorFactorHom O (leftUnitData I)) =
      CategoryTheory.Operad.UnitInsertion.leftInsertFromFactor
        (O.obj (ColoredProfile.oneColorFunctor.obj ⟨I⟩))
        (ColoredOperadObj.UnitInsertion.leftFactorHom O η
          (ColoredProfile.oneColorFunctor.obj ⟨I⟩))
  calc
    _ = CategoryTheory.Operad.UnitInsertion.leftInsertFromFactor
        ((uncolorCollection O).eval I)
        (CategoryTheory.Operad.UnitInsertion.leftFactorHom
            (uncolorCollection O) (uncolorUnit O η) I ≫
          uncolorFactorHom O (leftUnitData I)) :=
      CategoryTheory.Operad.UnitInsertion.leftInsertFromFactor_comp _ _ _
    _ = _ := by
      rw [uncolorLeftFactor_comp]
      with_unfolding_all rfl

end CategoryTheory.Operad.ColoredOperadObj.OneColor

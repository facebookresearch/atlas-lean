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

/-!
# Unit compatibility for color-blind operads

The colored right- and left-unit insertion routes for a color-blind collection agree with the
ordinary insertion routes after the canonical substitution-source comparison.
-/

@[expose] public section

namespace CategoryTheory.Operad.ColoredOperadObj.ColorBlind

open CategoryTheory

universe u v w

variable (Color : Type u)
variable {V : Type w} [Category.{v} V] [FiniteTensor V]

private theorem rightFactor_comp (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile Color) :
    ColoredOperadObj.UnitInsertion.rightFactorHom
        (collection Color O) (unitData Color O η) P ≫
      factorHom Color O (ColoredSubstitutionData.rightUnit P) =
        CategoryTheory.Operad.UnitInsertion.rightFactorHom O η P.inputs := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        apply heq_of_eq
        change ((FiniteTensor.singletonIso (V := V)).hom.app (O.eval P.inputs) ≫
            O.map (FinBijGroupoid.homOfEquiv (Equiv.refl P.inputs))) ≫ 𝟙 _ =
          (FiniteTensor.singletonIso (V := V)).hom.app (O.eval P.inputs)
        simp
    | some i =>
        apply heq_of_eq
        change η ≫ 𝟙 _ = η
        simp

private theorem leftFactor_comp (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile Color) :
    ColoredOperadObj.UnitInsertion.leftFactorHom
        (collection Color O) (unitData Color O η) P ≫
      factorHom Color O (ColoredSubstitutionData.leftUnit P) =
        CategoryTheory.Operad.UnitInsertion.leftFactorHom O η P.inputs := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        apply heq_of_eq
        change (η ≫ O.map (FinBijGroupoid.homOfEquiv (Equiv.refl arityOne))) ≫ 𝟙 _ = η
        simp
    | some i =>
        cases i
        apply heq_of_eq
        change (FiniteTensor.singletonIso (V := V)).hom.app (O.eval P.inputs) ≫ 𝟙 _ = _
        simp [CategoryTheory.Operad.UnitInsertion.leftFactorHom]

/-- The color-blind right-unit insertion followed by the source comparison is the ordinary
right-unit insertion. -/
theorem rightUnitInsert_compat (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile Color) :
    ColoredOperadObj.rightUnitInsert (collection Color O) (unitData Color O η) P ≫
        (sourceNatIso Color O).hom.app (ColoredSubstitutionData.rightUnit P) =
      CategoryTheory.Operad.rightUnitInsert O η P.inputs := by
  rw [rightUnitInsert_eq_insertFromFactor]
  have h := CategoryTheory.Operad.UnitInsertion.rightInsertFromFactor_comp
    ((collection Color O).obj P) P.inputs
    (ColoredOperadObj.UnitInsertion.rightFactorHom
      (collection Color O) (unitData Color O η) P)
    (factorHom Color O (ColoredSubstitutionData.rightUnit P))
  rw [rightFactor_comp] at h
  simp only [ColoredOperadObj.rightUnitInsert,
    sourceNatIso_hom_app, ColoredOperadObj.substitutionSource,
    CategoryTheory.Operad.substitutionSource, collection,
    ColoredProfile.arityFunctor, SymmetricCollection.eval, Functor.comp_obj]
  apply eq_of_heq
  exact heq_of_eq h

/-- The color-blind left-unit insertion followed by the source comparison is the ordinary left-unit
insertion. -/
theorem leftUnitInsert_compat (O : SymmetricCollection V) (η : OperadUnit O)
    (P : ColoredProfile Color) :
    ColoredOperadObj.leftUnitInsert (collection Color O) (unitData Color O η) P ≫
        (sourceNatIso Color O).hom.app (ColoredSubstitutionData.leftUnit P) =
      CategoryTheory.Operad.leftUnitInsert O η P.inputs := by
  rw [leftUnitInsert_eq_insertFromFactor]
  have h := CategoryTheory.Operad.UnitInsertion.leftInsertFromFactor_comp
    ((collection Color O).obj P)
    (ColoredOperadObj.UnitInsertion.leftFactorHom
      (collection Color O) (unitData Color O η) P)
    (factorHom Color O (ColoredSubstitutionData.leftUnit P))
  rw [leftFactor_comp] at h
  simp only [ColoredOperadObj.leftUnitInsert,
    sourceNatIso_hom_app, ColoredOperadObj.substitutionSource,
    CategoryTheory.Operad.substitutionSource, collection,
    ColoredProfile.arityFunctor, SymmetricCollection.eval, Functor.comp_obj]
  apply eq_of_heq
  exact heq_of_eq h

end CategoryTheory.Operad.ColoredOperadObj.ColorBlind

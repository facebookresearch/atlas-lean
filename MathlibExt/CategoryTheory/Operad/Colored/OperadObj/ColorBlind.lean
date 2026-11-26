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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlindAssociativity
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlindUnit
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Hom
public import MathlibExt.CategoryTheory.Operad.OperadObj.Hom

/-!
# Color-blind lifts of ordinary operads

Every ordinary operad determines a colored operad on any color type by forgetting all profile
colors and retaining only input arities. This construction is functorial in ordinary operads.
-/

@[expose] public section

namespace CategoryTheory.Operad.ColoredOperadObj.ColorBlind

open CategoryTheory

universe u v w

variable (Color : Type u)
variable {V : Type w} [Category.{v} V] [FiniteTensor V]

omit [FiniteTensor V] in
/-- The color-blind factor comparison is natural in a morphism of ordinary collections. -/
theorem factorHom_naturality {O P : SymmetricCollection V} (α : O ⟶ P)
    (d : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.factorHom
          (Functor.whiskerLeft (ColoredProfile.arityFunctor Color) α) d ≫
        factorHom Color P d =
      factorHom Color O d ≫
        OperadObj.HomData.factorHom α
          (ColoredSubstitutionData.toSubstitutionDataFunctor.obj d) := by
  let lhs := ColoredOperadObj.HomData.factorHom
      (Functor.whiskerLeft (ColoredProfile.arityFunctor Color) α) d ≫
    factorHom Color P d
  let rhs := factorHom Color O d ≫
    OperadObj.HomData.factorHom α
      (ColoredSubstitutionData.toSubstitutionDataFunctor.obj d)
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        let a := α.app ((ColoredProfile.arityFunctor Color).obj d.outerProfile)
        have hLeft : HEq (lhs.hom none) a := by
          with_unfolding_all exact heq_of_eq (Category.comp_id _)
        have hRight : HEq a (rhs.hom none) := by
          with_unfolding_all exact heq_of_eq (Category.id_comp _).symm
        exact hLeft.trans hRight
    | some i =>
        let a := α.app ((ColoredProfile.arityFunctor Color).obj (d.inner.obj i))
        have hLeft : HEq (lhs.hom (some i)) a := by
          with_unfolding_all exact heq_of_eq (Category.comp_id _)
        have hRight : HEq a (rhs.hom (some i)) := by
          with_unfolding_all exact heq_of_eq (Category.id_comp _).symm
        exact hLeft.trans hRight

/-- The color-blind substitution-source comparison is natural in an ordinary collection morphism. -/
theorem sourceHom_naturality {O P : SymmetricCollection V} (α : O ⟶ P)
    (d : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.sourceHom
          (Functor.whiskerLeft (ColoredProfile.arityFunctor Color) α) d ≫
        (sourceNatIso Color P).hom.app d =
      (sourceNatIso Color O).hom.app d ≫
        OperadObj.HomData.sourceHom α
          (ColoredSubstitutionData.toSubstitutionDataFunctor.obj d) := by
  let a := ColoredOperadObj.HomData.factorHom
    (Functor.whiskerLeft (ColoredProfile.arityFunctor Color) α) d
  let b :
      (ColoredOperadObj.substitutionFactors (collection Color P)).obj d ⟶
        (Operad.substitutionFactors P).obj
          (ColoredSubstitutionData.toSubstitutionDataFunctor.obj d) := by
    with_unfolding_all exact factorHom Color P d
  let c :
      (ColoredOperadObj.substitutionFactors (collection Color O)).obj d ⟶
        (Operad.substitutionFactors O).obj
          (ColoredSubstitutionData.toSubstitutionDataFunctor.obj d) := by
    with_unfolding_all exact factorHom Color O d
  let e := OperadObj.HomData.factorHom α
    (ColoredSubstitutionData.toSubstitutionDataFunctor.obj d)
  have h : a ≫ b = c ≫ e := by
    with_unfolding_all exact factorHom_naturality Color α d
  change (FiniteTensor.tensor (V := V)).map a ≫
      (FiniteTensor.tensor (V := V)).map b =
    (FiniteTensor.tensor (V := V)).map c ≫
      (FiniteTensor.tensor (V := V)).map e
  with_unfolding_all
    exact ((FiniteTensor.tensor (V := V)).map_comp a b).symm |>.trans
      ((congrArg (fun f => (FiniteTensor.tensor (V := V)).map f) h).trans
        ((FiniteTensor.tensor (V := V)).map_comp c e))

/-- Lift an ordinary operad to any color type by ignoring every profile color and retaining only
its finite input arity. -/
def obj (O : OperadObj V) : ColoredOperadObj Color V where
  toCollection := collection Color O.toCollection
  unit := unitData Color O.toCollection O.unit
  subst := substitutionData Color O.toCollection O.subst
  right_unit := by
    intro P
    let insertCol :
        O.toCollection.eval P.inputs ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color O.toCollection)).obj
              (ColoredSubstitutionData.rightUnit P)) := by
      with_unfolding_all
        exact (ColoredOperadObj.rightUnitInsert
          (collection Color O.toCollection) (unitData Color O.toCollection O.unit) P)
    let sourceIso :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color O.toCollection)).obj
              (ColoredSubstitutionData.rightUnit P)) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj (rightUnitData P.inputs)) := by
      with_unfolding_all
        exact (sourceNatIso Color O.toCollection).hom.app
          (ColoredSubstitutionData.rightUnit P)
    let insertOrd :
        O.toCollection.eval P.inputs ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj (rightUnitData P.inputs)) := by
      with_unfolding_all
        exact (Operad.rightUnitInsert O.toCollection O.unit P.inputs)
    let substOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj (rightUnitData P.inputs)) ⟶
          O.toCollection.eval (substitutionTotalObj (rightUnitData P.inputs)) :=
      O.subst.app (rightUnitData P.inputs)
    let substCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color O.toCollection)).obj
              (ColoredSubstitutionData.rightUnit P)) ⟶
          O.toCollection.eval (substitutionTotalObj (rightUnitData P.inputs)) := by
      with_unfolding_all
        exact (substitutionData Color O.toCollection O.subst).app
          (ColoredSubstitutionData.rightUnit P)
    let relabelOrd := O.toCollection.relabelIso (rightUnitTotalIso P.inputs)
    let relabelCol :
        O.toCollection.eval (substitutionTotalObj (rightUnitData P.inputs)) ⟶
          O.toCollection.eval P.inputs := by
      with_unfolding_all
        exact (collection Color O.toCollection).map
          (ColoredSubstitutionData.rightUnitTotalHom P)
    have hInsert : insertCol ≫ sourceIso = insertOrd := by
      with_unfolding_all exact rightUnitInsert_compat Color O.toCollection O.unit P
    have hSubst : sourceIso ≫ substOrd = substCol := by
      rfl
    have hPrefix : insertCol ≫ substCol = insertOrd ≫ substOrd := by
      rw [← hSubst, ← Category.assoc, hInsert]
    have hRelabel : relabelCol = relabelOrd := by
      rfl
    change insertCol ≫ substCol ≫ relabelCol = 𝟙 (O.toCollection.eval P.inputs)
    slice_lhs 1 2 => rw [hPrefix]
    rw [hRelabel]
    have hLaw : insertOrd ≫ substOrd ≫ relabelOrd = 𝟙 (O.toCollection.eval P.inputs) := by
      with_unfolding_all exact O.right_unit P.inputs
    exact (Category.assoc insertOrd substOrd relabelOrd).trans hLaw
  left_unit := by
    intro P
    let insertCol :
        O.toCollection.eval P.inputs ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color O.toCollection)).obj
              (ColoredSubstitutionData.leftUnit P)) := by
      with_unfolding_all
        exact (ColoredOperadObj.leftUnitInsert
          (collection Color O.toCollection) (unitData Color O.toCollection O.unit) P)
    let sourceIso :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color O.toCollection)).obj
              (ColoredSubstitutionData.leftUnit P)) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj (leftUnitData P.inputs)) := by
      with_unfolding_all
        exact (sourceNatIso Color O.toCollection).hom.app
          (ColoredSubstitutionData.leftUnit P)
    let insertOrd :
        O.toCollection.eval P.inputs ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj (leftUnitData P.inputs)) := by
      with_unfolding_all
        exact (Operad.leftUnitInsert O.toCollection O.unit P.inputs)
    let substOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj (leftUnitData P.inputs)) ⟶
          O.toCollection.eval (substitutionTotalObj (leftUnitData P.inputs)) :=
      O.subst.app (leftUnitData P.inputs)
    let substCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color O.toCollection)).obj
              (ColoredSubstitutionData.leftUnit P)) ⟶
          O.toCollection.eval (substitutionTotalObj (leftUnitData P.inputs)) := by
      with_unfolding_all
        exact (substitutionData Color O.toCollection O.subst).app
          (ColoredSubstitutionData.leftUnit P)
    let relabelOrd := O.toCollection.relabelIso (leftUnitTotalIso P.inputs)
    let relabelCol :
        O.toCollection.eval (substitutionTotalObj (leftUnitData P.inputs)) ⟶
          O.toCollection.eval P.inputs := by
      with_unfolding_all
        exact (collection Color O.toCollection).map
          (ColoredSubstitutionData.leftUnitTotalHom P)
    have hInsert : insertCol ≫ sourceIso = insertOrd := by
      with_unfolding_all exact leftUnitInsert_compat Color O.toCollection O.unit P
    have hSubst : sourceIso ≫ substOrd = substCol := by
      rfl
    have hPrefix : insertCol ≫ substCol = insertOrd ≫ substOrd := by
      rw [← hSubst, ← Category.assoc, hInsert]
    have hRelabel : relabelCol = relabelOrd := by
      rfl
    change insertCol ≫ substCol ≫ relabelCol = 𝟙 (O.toCollection.eval P.inputs)
    slice_lhs 1 2 => rw [hPrefix]
    rw [hRelabel]
    have hLaw : insertOrd ≫ substOrd ≫ relabelOrd = 𝟙 (O.toCollection.eval P.inputs) := by
      with_unfolding_all exact O.left_unit P.inputs
    exact (Category.assoc insertOrd substOrd relabelOrd).trans hLaw
  assoc := by
    intro d
    rw [← associativityRouteA_compat Color O.toCollection O.subst d,
      ← associativityRouteB_compat Color O.toCollection O.subst d,
      O.assoc (forgetColorsAssocData Color d)]

/-- Lift a morphism of ordinary operads. -/
def hom {O P : OperadObj V} (F : O ⟶ P) : obj Color O ⟶ obj Color P where
  toCollectionHom :=
    Functor.whiskerLeft (ColoredProfile.arityFunctor Color) F.toCollectionHom
  map_unit _ := by
    with_unfolding_all exact F.map_unit
  map_subst d := by
    let α := F.toCollectionHom
    let αc := Functor.whiskerLeft (ColoredProfile.arityFunctor Color) α
    let d₀ := ColoredSubstitutionData.toSubstitutionDataFunctor.obj d
    let sourceO :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color O.toCollection)).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj d₀) := by
      with_unfolding_all exact (sourceNatIso Color O.toCollection).hom.app d
    let sourceP :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color P.toCollection)).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors P.toCollection).obj d₀) := by
      with_unfolding_all exact (sourceNatIso Color P.toCollection).hom.app d
    let sourceMapCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color O.toCollection)).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color P.toCollection)).obj d) :=
      ColoredOperadObj.HomData.sourceHom αc d
    let sourceMapOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj d₀) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors P.toCollection).obj d₀) :=
      OperadObj.HomData.sourceHom α d₀
    let substOOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj d₀) ⟶
          O.toCollection.eval (substitutionTotalObj d₀) := O.subst.app d₀
    let substPOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors P.toCollection).obj d₀) ⟶
          P.toCollection.eval (substitutionTotalObj d₀) := P.subst.app d₀
    let substOCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color O.toCollection)).obj d) ⟶
          O.toCollection.eval (substitutionTotalObj d₀) := by
      with_unfolding_all exact (substitutionData Color O.toCollection O.subst).app d
    let substPCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors (collection Color P.toCollection)).obj d) ⟶
          P.toCollection.eval (substitutionTotalObj d₀) := by
      with_unfolding_all exact (substitutionData Color P.toCollection P.subst).app d
    let targetMap :
        O.toCollection.eval (substitutionTotalObj d₀) ⟶
          P.toCollection.eval (substitutionTotalObj d₀) :=
      α.app ⟨substitutionTotalObj d₀⟩
    have hSource : sourceMapCol ≫ sourceP = sourceO ≫ sourceMapOrd := by
      with_unfolding_all exact sourceHom_naturality Color α d
    have hSubstO : sourceO ≫ substOOrd = substOCol := by rfl
    have hSubstP : sourceP ≫ substPOrd = substPCol := by rfl
    have hMap : substOOrd ≫ targetMap = sourceMapOrd ≫ substPOrd := by
      with_unfolding_all exact F.map_subst d₀
    change substOCol ≫ targetMap = sourceMapCol ≫ substPCol
    with_unfolding_all
      calc
        _ = (sourceO ≫ substOOrd) ≫ targetMap :=
          congrArg (fun f => f ≫ targetMap) hSubstO.symm
        _ = sourceO ≫ (substOOrd ≫ targetMap) := Category.assoc _ _ _
        _ = sourceO ≫ (sourceMapOrd ≫ substPOrd) :=
          congrArg (fun f => sourceO ≫ f) hMap
        _ = (sourceO ≫ sourceMapOrd) ≫ substPOrd := (Category.assoc _ _ _).symm
        _ = (sourceMapCol ≫ sourceP) ≫ substPOrd :=
          congrArg (fun f => f ≫ substPOrd) hSource.symm
        _ = sourceMapCol ≫ (sourceP ≫ substPOrd) := Category.assoc _ _ _
        _ = sourceMapCol ≫ substPCol := congrArg (fun f => sourceMapCol ≫ f) hSubstP

/-- The color-blind lift as a functor from ordinary operads to colored operads. -/
def functor : OperadObj V ⥤ ColoredOperadObj Color V where
  obj := obj Color
  map := hom Color
  map_id O := by
    apply ColoredOperadObj.Hom.ext
    rfl
  map_comp F G := by
    apply ColoredOperadObj.Hom.ext
    rfl

/-- The color-blind lift acts on objects by `obj Color`. -/
@[simp]
theorem functor_obj (O : OperadObj V) :
    (functor Color).obj O = obj Color O :=
  rfl

/-- The color-blind lift acts on morphisms by `hom Color`. -/
@[simp]
theorem functor_map {O P : OperadObj V} (F : O ⟶ P) :
    (functor Color).map F = hom Color F :=
  rfl

/-- The color-blind lift transfers the right-unit law from an ordinary operad. -/
theorem isRightUnit (O : OperadObj V) :
    ColoredOperadObj.IsRightUnit (collection Color O.toCollection)
      (unitData Color O.toCollection O.unit) (substitutionData Color O.toCollection O.subst) :=
  (obj Color O).right_unit

/-- The color-blind lift transfers the left-unit law from an ordinary operad. -/
theorem isLeftUnit (O : OperadObj V) :
    ColoredOperadObj.IsLeftUnit (collection Color O.toCollection)
      (unitData Color O.toCollection O.unit) (substitutionData Color O.toCollection O.subst) :=
  (obj Color O).left_unit

/-- The color-blind lift transfers associativity from an ordinary operad. -/
theorem isAssociative (O : OperadObj V) :
    ColoredOperadObj.IsAssociative (collection Color O.toCollection)
      (substitutionData Color O.toCollection O.subst) :=
  (obj Color O).assoc

end CategoryTheory.Operad.ColoredOperadObj.ColorBlind

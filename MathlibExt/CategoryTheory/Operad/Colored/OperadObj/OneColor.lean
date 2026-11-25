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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlind
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Hom
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.OneColorAssociativity
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.OneColorUnit
public import MathlibExt.CategoryTheory.Operad.OperadObj.Hom

/-!
# Ordinary operads as one-colored operads

Colorization and forgetting define inverse equivalences between ordinary operads and colored
operads whose color type is `PUnit`. The construction records the comparison maps for substitution
sources explicitly, so morphism preservation and the unit and counit are stable under refactors of
the underlying finite-family implementation.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Operad.ColoredOperadObj.OneColor

universe w v c

variable {V : Type w} [Category.{v} V] [FiniteTensor V]


omit [FiniteTensor V] in
/-- The one-color factor comparison is natural in a morphism of ordinary collections. -/
theorem colorizeFactorHom_naturality {O P : SymmetricCollection V} (α : O ⟶ P)
    (d : ColoredSubstitutionData PUnit) :
    ColoredOperadObj.HomData.factorHom
          (Functor.whiskerLeft ColoredProfile.forgetOneColorFunctor α) d ≫
        colorizeFactorHom P d =
      colorizeFactorHom O d ≫
        OperadObj.HomData.factorHom α
          (ColoredSubstitutionData.forgetOneColorFunctor.obj d) :=
  ColoredOperadObj.ColorBlind.factorHom_naturality PUnit α d

/-- The one-color substitution-source comparison is natural in an ordinary collection morphism. -/
theorem colorizeSourceHom_naturality {O P : SymmetricCollection V} (α : O ⟶ P)
    (d : ColoredSubstitutionData PUnit) :
    ColoredOperadObj.HomData.sourceHom
          (Functor.whiskerLeft ColoredProfile.forgetOneColorFunctor α) d ≫
        (colorizeSourceNatIso P).hom.app d =
      (colorizeSourceNatIso O).hom.app d ≫
        OperadObj.HomData.sourceHom α
          (ColoredSubstitutionData.forgetOneColorFunctor.obj d) :=
  ColoredOperadObj.ColorBlind.sourceHom_naturality PUnit α d

omit [FiniteTensor V] in
/-- The one-color factor comparison is natural in a morphism of colored collections. -/
theorem uncolorFactorHom_naturality {O P : ColoredSymmetricCollection PUnit V} (α : O ⟶ P)
    (d : SubstitutionData) :
    OperadObj.HomData.factorHom
          (Functor.whiskerLeft ColoredProfile.oneColorFunctor α) d ≫
        uncolorFactorHom P d =
      uncolorFactorHom O d ≫
        ColoredOperadObj.HomData.factorHom α
          (ColoredSubstitutionData.oneColorFunctor.obj d) := by
  let lhs := OperadObj.HomData.factorHom
      (Functor.whiskerLeft ColoredProfile.oneColorFunctor α) d ≫
    uncolorFactorHom P d
  let rhs := uncolorFactorHom O d ≫
    ColoredOperadObj.HomData.factorHom α
      (ColoredSubstitutionData.oneColorFunctor.obj d)
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        let a := α.app (ColoredProfile.oneColorFunctor.obj ⟨d.index⟩)
        have hLeft : HEq (lhs.hom none) a := by
          with_unfolding_all exact heq_of_eq (Category.comp_id _)
        have hRight : HEq a (rhs.hom none) := by
          with_unfolding_all exact heq_of_eq (Category.id_comp _).symm
        exact hLeft.trans hRight
    | some i =>
        let a := α.app (ColoredProfile.oneColorFunctor.obj (d.obj i))
        have hLeft : HEq (lhs.hom (some i)) a := by
          with_unfolding_all exact heq_of_eq (Category.comp_id _)
        have hRight : HEq a (rhs.hom (some i)) := by
          with_unfolding_all exact heq_of_eq (Category.id_comp _).symm
        exact hLeft.trans hRight

/-- The one-color substitution-source comparison is natural in a colored collection morphism. -/
theorem uncolorSourceHom_naturality {O P : ColoredSymmetricCollection PUnit V} (α : O ⟶ P)
    (d : SubstitutionData) :
    OperadObj.HomData.sourceHom
          (Functor.whiskerLeft ColoredProfile.oneColorFunctor α) d ≫
        (uncolorSourceNatIso P).hom.app d =
      (uncolorSourceNatIso O).hom.app d ≫
        ColoredOperadObj.HomData.sourceHom α
          (ColoredSubstitutionData.oneColorFunctor.obj d) := by
  let a := OperadObj.HomData.factorHom
    (Functor.whiskerLeft ColoredProfile.oneColorFunctor α) d
  let b :
      (Operad.substitutionFactors (uncolorCollection P)).obj d ⟶
        (ColoredOperadObj.substitutionFactors P).obj
          (ColoredSubstitutionData.oneColorFunctor.obj d) := by
    with_unfolding_all exact uncolorFactorHom P d
  let c :
      (Operad.substitutionFactors (uncolorCollection O)).obj d ⟶
        (ColoredOperadObj.substitutionFactors O).obj
          (ColoredSubstitutionData.oneColorFunctor.obj d) := by
    with_unfolding_all exact uncolorFactorHom O d
  let e := ColoredOperadObj.HomData.factorHom α
    (ColoredSubstitutionData.oneColorFunctor.obj d)
  have h : a ≫ b = c ≫ e := by
    with_unfolding_all exact uncolorFactorHom_naturality α d
  change (FiniteTensor.tensor (V := V)).map a ≫
      (FiniteTensor.tensor (V := V)).map b =
    (FiniteTensor.tensor (V := V)).map c ≫
      (FiniteTensor.tensor (V := V)).map e
  with_unfolding_all
    exact ((FiniteTensor.tensor (V := V)).map_comp a b).symm |>.trans
      ((congrArg (fun f => (FiniteTensor.tensor (V := V)).map f) h).trans
        ((FiniteTensor.tensor (V := V)).map_comp c e))


/-- Regard an ordinary operad as a colored operad with the unique color in `PUnit`. -/
abbrev colorizeObj (O : OperadObj V) : ColoredOperadObj PUnit V :=
  ColoredOperadObj.ColorBlind.obj PUnit O

/-- Forget the unique color of a `PUnit`-colored operad. -/
def uncolorObj (O : ColoredOperadObj PUnit V) : OperadObj V where
  toCollection := uncolorCollection O.toCollection
  unit := uncolorUnit O.toCollection O.unit
  subst := uncolorSubst O.toCollection O.subst
  right_unit := by
    intro I
    let P := ColoredProfile.oneColorFunctor.obj ⟨I⟩
    let insertOrd :
        O.toCollection.obj P ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj
              (rightUnitData I)) := by
      with_unfolding_all
        exact (Operad.rightUnitInsert
          (uncolorCollection O.toCollection) (uncolorUnit O.toCollection O.unit) I)
    let sourceIso :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj
              (rightUnitData I)) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj
              (ColoredSubstitutionData.rightUnit P)) := by
      with_unfolding_all exact
        (uncolorSourceNatIso O.toCollection).hom.app (rightUnitData I)
    let insertCol :
        O.toCollection.obj P ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj
              (ColoredSubstitutionData.rightUnit P)) := by
      with_unfolding_all
        exact (ColoredOperadObj.rightUnitInsert O.toCollection O.unit P)
    let substCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj
              (ColoredSubstitutionData.rightUnit P)) ⟶
          O.toCollection.obj (ColoredSubstitutionData.rightUnit P).totalProfile :=
      O.subst.app (ColoredSubstitutionData.rightUnit P)
    let substOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj
              (rightUnitData I)) ⟶
          O.toCollection.obj (ColoredSubstitutionData.rightUnit P).totalProfile := by
      with_unfolding_all exact
        (uncolorSubst O.toCollection O.subst).app (rightUnitData I)
    let relabelCol := O.toCollection.map (ColoredSubstitutionData.rightUnitTotalHom P)
    let relabelOrd :
        O.toCollection.obj (ColoredSubstitutionData.rightUnit P).totalProfile ⟶
          O.toCollection.obj P := by
      with_unfolding_all exact
        (uncolorCollection O.toCollection).relabelIso (rightUnitTotalIso I)
    have hInsert : insertOrd ≫ sourceIso = insertCol := by
      with_unfolding_all exact uncolor_rightUnitInsert O.toCollection O.unit I
    have hSubst : sourceIso ≫ substCol = substOrd := by
      rfl
    have hPrefix : insertOrd ≫ substOrd = insertCol ≫ substCol := by
      rw [← hSubst, ← Category.assoc, hInsert]
    have hRelabel : relabelOrd = relabelCol := by
      rfl
    change insertOrd ≫ substOrd ≫ relabelOrd = 𝟙 (O.toCollection.obj P)
    slice_lhs 1 2 => rw [hPrefix]
    rw [hRelabel]
    have hLaw : insertCol ≫ substCol ≫ relabelCol = 𝟙 (O.toCollection.obj P) := by
      with_unfolding_all exact O.right_unit P
    exact (Category.assoc insertCol substCol relabelCol).trans hLaw
  left_unit := by
    intro I
    let P := ColoredProfile.oneColorFunctor.obj ⟨I⟩
    let insertOrd :
        O.toCollection.obj P ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj
              (leftUnitData I)) := by
      with_unfolding_all
        exact (Operad.leftUnitInsert
          (uncolorCollection O.toCollection) (uncolorUnit O.toCollection O.unit) I)
    let sourceIso :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj
              (leftUnitData I)) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj
              (ColoredSubstitutionData.leftUnit P)) := by
      with_unfolding_all exact
        (uncolorSourceNatIso O.toCollection).hom.app (leftUnitData I)
    let insertCol :
        O.toCollection.obj P ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj
              (ColoredSubstitutionData.leftUnit P)) := by
      with_unfolding_all
        exact (ColoredOperadObj.leftUnitInsert O.toCollection O.unit P)
    let substCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj
              (ColoredSubstitutionData.leftUnit P)) ⟶
          O.toCollection.obj (ColoredSubstitutionData.leftUnit P).totalProfile :=
      O.subst.app (ColoredSubstitutionData.leftUnit P)
    let substOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj
              (leftUnitData I)) ⟶
          O.toCollection.obj (ColoredSubstitutionData.leftUnit P).totalProfile := by
      with_unfolding_all exact
        (uncolorSubst O.toCollection O.subst).app (leftUnitData I)
    let relabelCol := O.toCollection.map (ColoredSubstitutionData.leftUnitTotalHom P)
    let relabelOrd :
        O.toCollection.obj (ColoredSubstitutionData.leftUnit P).totalProfile ⟶
          O.toCollection.obj P := by
      with_unfolding_all exact
        (uncolorCollection O.toCollection).relabelIso (leftUnitTotalIso I)
    have hInsert : insertOrd ≫ sourceIso = insertCol := by
      with_unfolding_all exact uncolor_leftUnitInsert O.toCollection O.unit I
    have hSubst : sourceIso ≫ substCol = substOrd := by
      rfl
    have hPrefix : insertOrd ≫ substOrd = insertCol ≫ substCol := by
      rw [← hSubst, ← Category.assoc, hInsert]
    have hRelabel : relabelOrd = relabelCol := by
      rfl
    change insertOrd ≫ substOrd ≫ relabelOrd = 𝟙 (O.toCollection.obj P)
    slice_lhs 1 2 => rw [hPrefix]
    rw [hRelabel]
    have hLaw : insertCol ≫ substCol ≫ relabelCol = 𝟙 (O.toCollection.obj P) := by
      with_unfolding_all exact O.left_unit P
    exact (Category.assoc insertCol substCol relabelCol).trans hLaw
  assoc := by
    intro d
    rw [← uncolorAssociativityRouteA_compat O.toCollection O.subst d,
      ← uncolorAssociativityRouteB_compat O.toCollection O.subst d,
      O.assoc (colorizeAssocData d)]

/-- Colorization transfers the right-unit law from an ordinary operad to its one-colored
counterpart. -/
theorem colorize_isRightUnit (O : OperadObj V) :
    ColoredOperadObj.IsRightUnit (colorizeCollection O.toCollection)
      (colorizeUnit O.toCollection O.unit) (colorizeSubst O.toCollection O.subst) :=
  (colorizeObj O).right_unit

/-- Colorization transfers the left-unit law from an ordinary operad to its one-colored
counterpart. -/
theorem colorize_isLeftUnit (O : OperadObj V) :
    ColoredOperadObj.IsLeftUnit (colorizeCollection O.toCollection)
      (colorizeUnit O.toCollection O.unit) (colorizeSubst O.toCollection O.subst) :=
  (colorizeObj O).left_unit

/-- Colorization transfers associativity from an ordinary operad to its one-colored
counterpart. -/
theorem colorize_isAssociative (O : OperadObj V) :
    ColoredOperadObj.IsAssociative (colorizeCollection O.toCollection)
      (colorizeSubst O.toCollection O.subst) :=
  (colorizeObj O).assoc

/-- Forgetting the unique color transfers the right-unit law to the underlying ordinary
operad. -/
theorem uncolor_isRightUnit (O : ColoredOperadObj PUnit V) :
    CategoryTheory.Operad.IsRightUnit (uncolorCollection O.toCollection)
      (uncolorUnit O.toCollection O.unit) (uncolorSubst O.toCollection O.subst) :=
  (uncolorObj O).right_unit

/-- Forgetting the unique color transfers the left-unit law to the underlying ordinary
operad. -/
theorem uncolor_isLeftUnit (O : ColoredOperadObj PUnit V) :
    CategoryTheory.Operad.IsLeftUnit (uncolorCollection O.toCollection)
      (uncolorUnit O.toCollection O.unit) (uncolorSubst O.toCollection O.subst) :=
  (uncolorObj O).left_unit

/-- Forgetting the unique color transfers associativity to the underlying ordinary operad. -/
theorem uncolor_isAssociative (O : ColoredOperadObj PUnit V) :
    CategoryTheory.Operad.IsAssociative (uncolorCollection O.toCollection)
      (uncolorSubst O.toCollection O.subst) :=
  (uncolorObj O).assoc

/-- Colorize a morphism of ordinary operads. -/
abbrev colorizeHom {O P : OperadObj V} (F : O ⟶ P) : colorizeObj O ⟶ colorizeObj P :=
  ColoredOperadObj.ColorBlind.hom PUnit F

/-- Colorization as a functor from ordinary operads to one-colored operads. -/
abbrev colorizeFunctor : OperadObj V ⥤ ColoredOperadObj PUnit V :=
  ColoredOperadObj.ColorBlind.functor PUnit

/-- Colorization acts on objects by `colorizeObj`. -/
@[simp]
theorem colorizeFunctor_obj (O : OperadObj V) :
    colorizeFunctor.obj O = colorizeObj O :=
  rfl

/-- Colorization acts on morphisms by `colorizeHom`. -/
@[simp]
theorem colorizeFunctor_map {O P : OperadObj V} (F : O ⟶ P) :
    colorizeFunctor.map F = colorizeHom F :=
  rfl

/-- Forget the unique color from a morphism of one-colored operads. -/
def uncolorHom {O P : ColoredOperadObj PUnit V} (F : O ⟶ P) :
    uncolorObj O ⟶ uncolorObj P where
  toCollectionHom := Functor.whiskerLeft ColoredProfile.oneColorFunctor F.toCollectionHom
  map_unit := by
    with_unfolding_all exact F.map_unit PUnit.unit
  map_subst d := by
    let α := F.toCollectionHom
    let αu := Functor.whiskerLeft ColoredProfile.oneColorFunctor α
    let d₁ := ColoredSubstitutionData.oneColorFunctor.obj d
    let sourceO :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) := by
      with_unfolding_all exact (uncolorSourceNatIso O.toCollection).hom.app d
    let sourceP :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection P.toCollection)).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors P.toCollection).obj d₁) := by
      with_unfolding_all exact (uncolorSourceNatIso P.toCollection).hom.app d
    let sourceMapOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection P.toCollection)).obj d) :=
      OperadObj.HomData.sourceHom αu d
    let sourceMapCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors P.toCollection).obj d₁) :=
      ColoredOperadObj.HomData.sourceHom α d₁
    let substOCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) ⟶
          O.toCollection.obj d₁.totalProfile := O.subst.app d₁
    let substPCol :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors P.toCollection).obj d₁) ⟶
          P.toCollection.obj d₁.totalProfile := P.subst.app d₁
    let substOOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj d) ⟶
          O.toCollection.obj d₁.totalProfile := by
      with_unfolding_all exact (uncolorSubst O.toCollection O.subst).app d
    let substPOrd :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection P.toCollection)).obj d) ⟶
          P.toCollection.obj d₁.totalProfile := by
      with_unfolding_all exact (uncolorSubst P.toCollection P.subst).app d
    let targetMap : O.toCollection.obj d₁.totalProfile ⟶ P.toCollection.obj d₁.totalProfile :=
      α.app d₁.totalProfile
    have hSource : sourceMapOrd ≫ sourceP = sourceO ≫ sourceMapCol := by
      with_unfolding_all exact uncolorSourceHom_naturality α d
    have hSubstO : sourceO ≫ substOCol = substOOrd := by rfl
    have hSubstP : sourceP ≫ substPCol = substPOrd := by rfl
    have hMap : substOCol ≫ targetMap = sourceMapCol ≫ substPCol := by
      with_unfolding_all exact F.map_subst d₁
    change substOOrd ≫ targetMap = sourceMapOrd ≫ substPOrd
    with_unfolding_all
      calc
        _ = (sourceO ≫ substOCol) ≫ targetMap :=
          congrArg (fun f => f ≫ targetMap) hSubstO.symm
        _ = sourceO ≫ (substOCol ≫ targetMap) := Category.assoc _ _ _
        _ = sourceO ≫ (sourceMapCol ≫ substPCol) :=
          congrArg (fun f => sourceO ≫ f) hMap
        _ = (sourceO ≫ sourceMapCol) ≫ substPCol := (Category.assoc _ _ _).symm
        _ = (sourceMapOrd ≫ sourceP) ≫ substPCol :=
          congrArg (fun f => f ≫ substPCol) hSource.symm
        _ = sourceMapOrd ≫ (sourceP ≫ substPCol) := Category.assoc _ _ _
        _ = sourceMapOrd ≫ substPOrd := congrArg (fun f => sourceMapOrd ≫ f) hSubstP

/-- Forgetting the unique color as a functor from one-colored operads to ordinary operads. -/
def uncolorFunctor : ColoredOperadObj PUnit V ⥤ OperadObj V where
  obj := uncolorObj
  map := uncolorHom
  map_id O := by
    apply OperadObj.Hom.ext
    rfl

  map_comp F G := by
    apply OperadObj.Hom.ext
    rfl

/-- Forgetting the unique color acts on objects by `uncolorObj`. -/
@[simp]
theorem uncolorFunctor_obj (O : ColoredOperadObj PUnit V) :
    uncolorFunctor.obj O = uncolorObj O :=
  rfl

/-- Forgetting the unique color acts on morphisms by `uncolorHom`. -/
@[simp]
theorem uncolorFunctor_map {O P : ColoredOperadObj PUnit V} (F : O ⟶ P) :
    uncolorFunctor.map F = uncolorHom F :=
  rfl

/-- Source compatibility for the forward ordinary round-trip comparison. -/
theorem ordinaryUnitSource_hom (O : SymmetricCollection V) (d : SubstitutionData) :
    OperadObj.HomData.sourceHom (ordinaryCollectionUnitIso O).hom d ≫
        (uncolorSourceNatIso (colorizeCollection O)).hom.app d ≫
        (colorizeSourceNatIso O).hom.app
          (ColoredSubstitutionData.oneColorFunctor.obj d) =
      𝟙 ((Operad.substitutionSource O).obj d) := by
  let a := OperadObj.HomData.factorHom (ordinaryCollectionUnitIso O).hom d
  let b :
      (Operad.substitutionFactors (uncolorCollection (colorizeCollection O))).obj d ⟶
        (ColoredOperadObj.substitutionFactors (colorizeCollection O)).obj
          (ColoredSubstitutionData.oneColorFunctor.obj d) := by
    with_unfolding_all exact uncolorFactorHom (colorizeCollection O) d
  let c :
      (ColoredOperadObj.substitutionFactors (colorizeCollection O)).obj
          (ColoredSubstitutionData.oneColorFunctor.obj d) ⟶
        (Operad.substitutionFactors O).obj d := by
    with_unfolding_all
      exact colorizeFactorHom O (ColoredSubstitutionData.oneColorFunctor.obj d)
  have hFamily : (a ≫ b) ≫ c = 𝟙 ((Operad.substitutionFactors O).obj d) := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro o
      cases o with
      | none =>
          with_unfolding_all
            change HEq (((𝟙 _) ≫ (𝟙 _)) ≫ (𝟙 _)) (𝟙 _)
            exact heq_of_eq (by simp)
      | some i =>
          with_unfolding_all
            change HEq (((𝟙 _) ≫ (𝟙 _)) ≫ (𝟙 _)) (𝟙 _)
            exact heq_of_eq (by simp)
  change (FiniteTensor.tensor (V := V)).map a ≫
      (FiniteTensor.tensor (V := V)).map b ≫
      (FiniteTensor.tensor (V := V)).map c = 𝟙 _
  rw [← Category.assoc, ← (FiniteTensor.tensor (V := V)).map_comp,
    ← (FiniteTensor.tensor (V := V)).map_comp, hFamily,
    (FiniteTensor.tensor (V := V)).map_id]

/-- Source compatibility for the inverse ordinary round-trip comparison. -/
theorem ordinaryUnitSource_inv (O : SymmetricCollection V) (d : SubstitutionData) :
    (uncolorSourceNatIso (colorizeCollection O)).hom.app d ≫
        (colorizeSourceNatIso O).hom.app
          (ColoredSubstitutionData.oneColorFunctor.obj d) =
      OperadObj.HomData.sourceHom (ordinaryCollectionUnitIso O).inv d := by
  let a :
      (Operad.substitutionFactors (uncolorCollection (colorizeCollection O))).obj d ⟶
        (ColoredOperadObj.substitutionFactors (colorizeCollection O)).obj
          (ColoredSubstitutionData.oneColorFunctor.obj d) := by
    with_unfolding_all exact uncolorFactorHom (colorizeCollection O) d
  let b :
      (ColoredOperadObj.substitutionFactors (colorizeCollection O)).obj
          (ColoredSubstitutionData.oneColorFunctor.obj d) ⟶
        (Operad.substitutionFactors O).obj d := by
    with_unfolding_all
      exact colorizeFactorHom O (ColoredSubstitutionData.oneColorFunctor.obj d)
  let c := OperadObj.HomData.factorHom (ordinaryCollectionUnitIso O).inv d
  have hFamily : a ≫ b = c := by
    apply FiniteFamily.Hom_ext
    · rfl
    · intro o
      cases o with
      | none =>
          with_unfolding_all
            change HEq ((𝟙 _) ≫ (𝟙 _)) (𝟙 _)
            exact heq_of_eq (Category.comp_id _)
      | some i =>
          with_unfolding_all
            change HEq ((𝟙 _) ≫ (𝟙 _)) (𝟙 _)
            exact heq_of_eq (Category.comp_id _)
  change (FiniteTensor.tensor (V := V)).map a ≫
      (FiniteTensor.tensor (V := V)).map b =
    (FiniteTensor.tensor (V := V)).map c
  rw [← (FiniteTensor.tensor (V := V)).map_comp, hFamily]

/-- Source compatibility for the forward colored round-trip comparison. -/
theorem coloredCounitSource_hom (O : ColoredSymmetricCollection PUnit V)
    (d : ColoredSubstitutionData PUnit) :
    (colorizeSourceNatIso (uncolorCollection O)).hom.app d ≫
        (uncolorSourceNatIso O).hom.app
          (ColoredSubstitutionData.forgetOneColorFunctor.obj d) ≫
        (ColoredOperadObj.substitutionSource O).map
          (ColoredSubstitutionData.oneColorCounitHom d) =
      ColoredOperadObj.HomData.sourceHom (coloredCollectionCounitIso O).hom d := by
  let d₀ := ColoredSubstitutionData.forgetOneColorFunctor.obj d
  let d₁ := ColoredSubstitutionData.oneColorFunctor.obj d₀
  let a :
      (ColoredOperadObj.substitutionFactors (colorizeCollection (uncolorCollection O))).obj d ⟶
        (Operad.substitutionFactors (uncolorCollection O)).obj d₀ := by
    with_unfolding_all exact colorizeFactorHom (uncolorCollection O) d
  let b :
      (Operad.substitutionFactors (uncolorCollection O)).obj d₀ ⟶
        (ColoredOperadObj.substitutionFactors O).obj d₁ := by
    with_unfolding_all exact uncolorFactorHom O d₀
  let c := (ColoredOperadObj.substitutionFactors O).map
    (ColoredSubstitutionData.oneColorCounitHom d)
  let e := ColoredOperadObj.HomData.factorHom (coloredCollectionCounitIso O).hom d
  have hFamily : (a ≫ b) ≫ c = e := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro x
      cases x <;> rfl
    · intro o
      cases o with
      | none =>
          let m := O.map (ColoredProfile.oneColorCounitHom d.outerProfile)
          have hLeft : HEq (((a ≫ b) ≫ c).hom none) m := by
            have h0 : HEq (((a ≫ b) ≫ c).hom none) (((𝟙 _) ≫ (𝟙 _)) ≫ m) := by
              with_unfolding_all exact heq_of_eq rfl
            have h1 : HEq (((𝟙 _) ≫ (𝟙 _)) ≫ m) m := by
              exact heq_of_eq (by rw [Category.id_comp, Category.id_comp])
            exact h0.trans h1
          have hRight : HEq m (e.hom none) := by
            have h0 : HEq (e.hom none) m := by
              with_unfolding_all
                exact heq_of_eq (coloredCollectionCounitIso_hom_app O d.outerProfile)
            exact h0.symm
          exact hLeft.trans hRight
      | some i =>
          let m := O.map (ColoredProfile.oneColorCounitHom (d.inner.obj i))
          have hLeft : HEq (((a ≫ b) ≫ c).hom (some i)) m := by
            have h0 : HEq (((a ≫ b) ≫ c).hom (some i)) (((𝟙 _) ≫ (𝟙 _)) ≫ m) := by
              with_unfolding_all exact heq_of_eq rfl
            have h1 : HEq (((𝟙 _) ≫ (𝟙 _)) ≫ m) m := by
              exact heq_of_eq (by rw [Category.id_comp, Category.id_comp])
            exact h0.trans h1
          have hRight : HEq m (e.hom (some i)) := by
            have h0 : HEq (e.hom (some i)) m := by
              with_unfolding_all
                exact heq_of_eq (coloredCollectionCounitIso_hom_app O (d.inner.obj i))
            exact h0.symm
          exact hLeft.trans hRight
  change (FiniteTensor.tensor (V := V)).map a ≫
      (FiniteTensor.tensor (V := V)).map b ≫
      (FiniteTensor.tensor (V := V)).map c =
    (FiniteTensor.tensor (V := V)).map e
  rw [← Category.assoc, ← (FiniteTensor.tensor (V := V)).map_comp,
    ← (FiniteTensor.tensor (V := V)).map_comp, hFamily]

/-- Source compatibility for the inverse colored round-trip comparison. -/
theorem coloredCounitSource_inv (O : ColoredSymmetricCollection PUnit V)
    (d : ColoredSubstitutionData PUnit) :
    (ColoredOperadObj.substitutionSource O).map
          (ColoredSubstitutionData.oneColorCounitInv d) ≫
        (uncolorSourceNatIso O).inv.app
          (ColoredSubstitutionData.forgetOneColorFunctor.obj d) ≫
        (colorizeSourceNatIso (uncolorCollection O)).inv.app d =
      ColoredOperadObj.HomData.sourceHom (coloredCollectionCounitIso O).inv d := by
  let d₀ := ColoredSubstitutionData.forgetOneColorFunctor.obj d
  let d₁ := ColoredSubstitutionData.oneColorFunctor.obj d₀
  let a := (ColoredOperadObj.substitutionFactors O).map
    (ColoredSubstitutionData.oneColorCounitInv d)
  let b :
      (ColoredOperadObj.substitutionFactors O).obj d₁ ⟶
        (Operad.substitutionFactors (uncolorCollection O)).obj d₀ := by
    with_unfolding_all exact (uncolorFactorIso O d₀).inv
  let c :
      (Operad.substitutionFactors (uncolorCollection O)).obj d₀ ⟶
        (ColoredOperadObj.substitutionFactors
          (colorizeCollection (uncolorCollection O))).obj d := by
    with_unfolding_all exact (colorizeFactorIso (uncolorCollection O) d).inv
  let e := ColoredOperadObj.HomData.factorHom (coloredCollectionCounitIso O).inv d
  have hFamily : (a ≫ b) ≫ c = e := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro x
      cases x <;> rfl
    · intro o
      cases o with
      | none =>
          let m := O.map (Groupoid.inv (ColoredProfile.oneColorCounitHom d.outerProfile))
          have hLeft : HEq (((a ≫ b) ≫ c).hom none) m := by
            have ha : HEq (a.hom none) m := by
              with_unfolding_all exact heq_of_eq rfl
            have hb : HEq (b.hom (a.equiv none))
                (𝟙 (O.obj ((ColoredProfile.forgetOneColorFunctor ⋙
                  ColoredProfile.oneColorFunctor).obj d.outerProfile))) := by
              with_unfolding_all exact eqToHom_comp_heq _ _
            have hc : HEq (c.hom ((a.equiv.trans b.equiv) none))
                (𝟙 (O.obj ((ColoredProfile.forgetOneColorFunctor ⋙
                  ColoredProfile.oneColorFunctor).obj d.outerProfile))) := by
              with_unfolding_all exact eqToHom_comp_heq _ _
            have hab := heq_comp rfl rfl rfl ha hb
            have habc := heq_comp rfl rfl rfl hab hc
            let X : V := O.obj ((ColoredProfile.forgetOneColorFunctor ⋙
              ColoredProfile.oneColorFunctor).obj d.outerProfile)
            have hcomp : (m ≫ 𝟙 X) ≫ 𝟙 X = m := by
              rw [Category.comp_id, Category.comp_id]
            exact habc.trans (heq_of_eq hcomp)
          have hRight : HEq m (e.hom none) := by
            have h0 : HEq (e.hom none) m := by
              with_unfolding_all
                exact heq_of_eq (coloredCollectionCounitIso_inv_app O d.outerProfile)
            exact h0.symm
          exact hLeft.trans hRight
      | some i =>
          let m := O.map (Groupoid.inv (ColoredProfile.oneColorCounitHom (d.inner.obj i)))
          have hLeft : HEq (((a ≫ b) ≫ c).hom (some i)) m := by
            have ha : HEq (a.hom (some i)) m := by
              with_unfolding_all exact heq_of_eq rfl
            have hb : HEq (b.hom (a.equiv (some i)))
                (𝟙 (O.obj ((ColoredProfile.forgetOneColorFunctor ⋙
                  ColoredProfile.oneColorFunctor).obj (d.inner.obj i)))) := by
              with_unfolding_all exact eqToHom_comp_heq _ _
            have hc : HEq (c.hom ((a.equiv.trans b.equiv) (some i)))
                (𝟙 (O.obj ((ColoredProfile.forgetOneColorFunctor ⋙
                  ColoredProfile.oneColorFunctor).obj (d.inner.obj i)))) := by
              with_unfolding_all exact eqToHom_comp_heq _ _
            have hab := heq_comp rfl rfl rfl ha hb
            have habc := heq_comp rfl rfl rfl hab hc
            let X : V := O.obj ((ColoredProfile.forgetOneColorFunctor ⋙
              ColoredProfile.oneColorFunctor).obj (d.inner.obj i))
            have hcomp : (m ≫ 𝟙 X) ≫ 𝟙 X = m := by
              rw [Category.comp_id, Category.comp_id]
            exact habc.trans (heq_of_eq hcomp)
          have hRight : HEq m (e.hom (some i)) := by
            have h0 : HEq (e.hom (some i)) m := by
              with_unfolding_all
                exact heq_of_eq (coloredCollectionCounitIso_inv_app O (d.inner.obj i))
            exact h0.symm
          exact hLeft.trans hRight
  change (FiniteTensor.tensor (V := V)).map a ≫
      (FiniteTensor.tensor (V := V)).map b ≫
      (FiniteTensor.tensor (V := V)).map c =
    (FiniteTensor.tensor (V := V)).map e
  rw [← Category.assoc, ← (FiniteTensor.tensor (V := V)).map_comp,
    ← (FiniteTensor.tensor (V := V)).map_comp, hFamily]

/-- The substitution-data counit induces the profile counit on total profiles. -/
@[simp]
theorem oneColorCounitHom_totalProfile (d : ColoredSubstitutionData PUnit) :
    ColoredSubstitutionData.totalProfileMap
        (ColoredSubstitutionData.oneColorCounitHom d) =
      ColoredProfile.oneColorCounitHom d.totalProfile := by
  apply ColoredProfile.Hom.ext
  rfl

/-- The inverse substitution-data counit induces the inverse profile counit on total profiles. -/
@[simp]
theorem oneColorCounitInv_totalProfile (d : ColoredSubstitutionData PUnit) :
    ColoredSubstitutionData.totalProfileMap
        (ColoredSubstitutionData.oneColorCounitInv d) =
      Groupoid.inv (ColoredProfile.oneColorCounitHom d.totalProfile) := by
  apply ColoredProfile.Hom.ext
  rfl

/-- The counit comparison as a morphism of one-colored operads. -/
noncomputable def coloredCounitHom (O : ColoredOperadObj PUnit V) :
    colorizeObj (uncolorObj O) ⟶ O where
  toCollectionHom := (coloredCollectionCounitIso O.toCollection).hom
  map_unit c := by
    cases c
    let unitMap : O.toCollection.obj (ColoredSubstitutionData.unitProfile PUnit.unit) ⟶
        O.toCollection.obj (ColoredSubstitutionData.unitProfile PUnit.unit) := by
      with_unfolding_all exact
        ((coloredCollectionCounitIso O.toCollection).hom.app
          (ColoredSubstitutionData.unitProfile PUnit.unit))
    have hUnitMap : unitMap = 𝟙 _ := by
      dsimp only [unitMap]
      rw [coloredCollectionCounitIso_hom_app]
      rw [show ColoredProfile.oneColorCounitHom
          (ColoredSubstitutionData.unitProfile PUnit.unit) = 𝟙 _ by
        apply ColoredProfile.Hom.ext
        rfl]
      exact O.toCollection.map_id _
    change O.unit PUnit.unit ≫ unitMap = O.unit PUnit.unit
    rw [hUnitMap, Category.comp_id]
  map_subst d := by
    let d₀ := ColoredSubstitutionData.forgetOneColorFunctor.obj d
    let d₁ := ColoredSubstitutionData.oneColorFunctor.obj d₀
    let δ := ColoredSubstitutionData.oneColorCounitHom d
    let source₁ :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection (uncolorCollection O.toCollection))).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj d₀) := by
      with_unfolding_all exact
        (colorizeSourceNatIso (uncolorCollection O.toCollection)).hom.app d
    let source₂ :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj d₀) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) := by
      with_unfolding_all exact (uncolorSourceNatIso O.toCollection).hom.app d₀
    let sourceδ :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d) := by
      with_unfolding_all exact
        (ColoredOperadObj.substitutionSource O.toCollection).map δ
    let sourceMap :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection (uncolorCollection O.toCollection))).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d) :=
      ColoredOperadObj.HomData.sourceHom (coloredCollectionCounitIso O.toCollection).hom d
    let subst₁ :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) ⟶
          O.toCollection.obj d₁.totalProfile := O.subst.app d₁
    let subst :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d) ⟶
          O.toCollection.obj d.totalProfile := O.subst.app d
    let substRound :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection (uncolorCollection O.toCollection))).obj d) ⟶
          O.toCollection.obj d₁.totalProfile := by
      with_unfolding_all exact (colorizeObj (uncolorObj O)).subst.app d
    let targetMap : O.toCollection.obj d₁.totalProfile ⟶ O.toCollection.obj d.totalProfile := by
      with_unfolding_all exact
        (coloredCollectionCounitIso O.toCollection).hom.app d.totalProfile
    have hSource : source₁ ≫ source₂ ≫ sourceδ = sourceMap :=
      coloredCounitSource_hom O.toCollection d
    have hRound : source₁ ≫ source₂ ≫ subst₁ = substRound := by
      rfl
    have hTarget :
        (ColoredOperadObj.substitutionTarget O.toCollection).map δ = targetMap := by
      dsimp only [targetMap]
      rw [coloredCollectionCounitIso_hom_app]
      change O.toCollection.map (ColoredSubstitutionData.totalProfileMap δ) =
        O.toCollection.map (ColoredProfile.oneColorCounitHom d.totalProfile)
      rw [show ColoredSubstitutionData.totalProfileMap δ =
          ColoredProfile.oneColorCounitHom d.totalProfile by
        exact oneColorCounitHom_totalProfile d]
      rfl
    have hNat : sourceδ ≫ subst = subst₁ ≫ targetMap := by
      rw [← hTarget]
      exact O.subst.naturality δ
    change substRound ≫ targetMap = sourceMap ≫ subst
    rw [← hRound]
    slice_lhs 3 4 => rw [← hNat]
    slice_lhs 1 3 => rw [hSource]

/-- The inverse counit comparison as a morphism of one-colored operads. -/
noncomputable def coloredCounitInv (O : ColoredOperadObj PUnit V) :
    O ⟶ colorizeObj (uncolorObj O) where
  toCollectionHom := (coloredCollectionCounitIso O.toCollection).inv
  map_unit c := by
    cases c
    let unitMap : O.toCollection.obj (ColoredSubstitutionData.unitProfile PUnit.unit) ⟶
        O.toCollection.obj (ColoredSubstitutionData.unitProfile PUnit.unit) := by
      with_unfolding_all exact
        ((coloredCollectionCounitIso O.toCollection).inv.app
          (ColoredSubstitutionData.unitProfile PUnit.unit))
    have hUnitMap : unitMap = 𝟙 _ := by
      dsimp only [unitMap]
      rw [coloredCollectionCounitIso_inv_app]
      rw [show Groupoid.inv (ColoredProfile.oneColorCounitHom
          (ColoredSubstitutionData.unitProfile PUnit.unit)) = 𝟙 _ by
        apply ColoredProfile.Hom.ext
        rfl]
      exact O.toCollection.map_id _
    change O.unit PUnit.unit ≫ unitMap = O.unit PUnit.unit
    rw [hUnitMap, Category.comp_id]
  map_subst d := by
    let d₀ := ColoredSubstitutionData.forgetOneColorFunctor.obj d
    let d₁ := ColoredSubstitutionData.oneColorFunctor.obj d₀
    let δ := ColoredSubstitutionData.oneColorCounitHom d
    let δinv := ColoredSubstitutionData.oneColorCounitInv d
    let source₁ :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection (uncolorCollection O.toCollection))).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj d₀) := by
      with_unfolding_all exact
        (colorizeSourceNatIso (uncolorCollection O.toCollection)).hom.app d
    let source₂ :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj d₀) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) := by
      with_unfolding_all exact (uncolorSourceNatIso O.toCollection).hom.app d₀
    let sourceδinv :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) := by
      with_unfolding_all exact
        (ColoredOperadObj.substitutionSource O.toCollection).map δinv
    let source₂Inv :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj d₀) := by
      with_unfolding_all exact (uncolorSourceNatIso O.toCollection).inv.app d₀
    let source₁Inv :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors (uncolorCollection O.toCollection)).obj d₀) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection (uncolorCollection O.toCollection))).obj d) := by
      with_unfolding_all exact
        (colorizeSourceNatIso (uncolorCollection O.toCollection)).inv.app d
    let sourceMap :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection (uncolorCollection O.toCollection))).obj d) :=
      ColoredOperadObj.HomData.sourceHom (coloredCollectionCounitIso O.toCollection).inv d
    let subst₁ :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d₁) ⟶
          O.toCollection.obj d₁.totalProfile := O.subst.app d₁
    let subst :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors O.toCollection).obj d) ⟶
          O.toCollection.obj d.totalProfile := O.subst.app d
    let substRound :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection (uncolorCollection O.toCollection))).obj d) ⟶
          O.toCollection.obj d₁.totalProfile := by
      with_unfolding_all exact (colorizeObj (uncolorObj O)).subst.app d
    let targetMap : O.toCollection.obj d.totalProfile ⟶ O.toCollection.obj d₁.totalProfile := by
      with_unfolding_all exact
        (coloredCollectionCounitIso O.toCollection).inv.app d.totalProfile
    have hSourceInv :
        sourceδinv ≫ source₂Inv ≫ source₁Inv = sourceMap := by
      with_unfolding_all exact coloredCounitSource_inv O.toCollection d
    have hRound : source₁ ≫ source₂ ≫ subst₁ = substRound := by
      rfl
    have hTarget :
        (ColoredOperadObj.substitutionTarget O.toCollection).map δinv = targetMap := by
      dsimp only [targetMap]
      rw [coloredCollectionCounitIso_inv_app]
      change O.toCollection.map (ColoredSubstitutionData.totalProfileMap δinv) =
        O.toCollection.map
          (Groupoid.inv (ColoredProfile.oneColorCounitHom d.totalProfile))
      rw [show ColoredSubstitutionData.totalProfileMap δinv =
          Groupoid.inv (ColoredProfile.oneColorCounitHom d.totalProfile) by
        exact oneColorCounitInv_totalProfile d]
      rfl
    have hNat : sourceδinv ≫ subst₁ = subst ≫ targetMap := by
      rw [← hTarget]
      exact O.subst.naturality δinv
    have hCancel₁ : source₁Inv ≫ source₁ = 𝟙 _ := by
      with_unfolding_all exact
        (colorizeSourceNatIso (uncolorCollection O.toCollection)).inv_hom_id_app d
    have hCancel₂ : source₂Inv ≫ source₂ = 𝟙 _ := by
      with_unfolding_all exact (uncolorSourceNatIso O.toCollection).inv_hom_id_app d₀
    have hSourceCancel : sourceMap ≫ source₁ ≫ source₂ = sourceδinv := by
      rw [← hSourceInv]
      calc
        (sourceδinv ≫ source₂Inv ≫ source₁Inv) ≫ source₁ ≫ source₂ =
            sourceδinv ≫ source₂Inv ≫ ((source₁Inv ≫ source₁) ≫ source₂) := by
          simp only [Category.assoc]
        _ = sourceδinv ≫ source₂Inv ≫ source₂ := by
          rw [hCancel₁, Category.id_comp]
        _ = sourceδinv ≫ (source₂Inv ≫ source₂) := rfl
        _ = sourceδinv := by rw [hCancel₂, Category.comp_id]
    change subst ≫ targetMap = sourceMap ≫ substRound
    rw [← hNat, ← hRound]
    slice_rhs 1 3 => rw [hSourceCancel]

/-- The unit comparison as a morphism of ordinary operads. -/
noncomputable def ordinaryUnitHom (O : OperadObj V) :
    O ⟶ uncolorObj.{w, v, c} (colorizeObj.{w, v, c} O) where
  toCollectionHom := (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).hom
  map_unit := by
    let unitMap : O.toCollection.eval arityOne ⟶ O.toCollection.eval arityOne := by
      with_unfolding_all exact
        (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).hom.app ⟨arityOne⟩
    have hUnitMap : unitMap = 𝟙 _ := by rfl
    change O.unit ≫ unitMap = O.unit
    rw [hUnitMap, Category.comp_id]
  map_subst d := by
    let α := (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).hom
    let sourceMap :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors
              (uncolorCollection.{w, v, c}
                (colorizeCollection.{w, v, c} O.toCollection))).obj d) :=
      OperadObj.HomData.sourceHom α d
    let source₁ :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors
              (uncolorCollection.{w, v, c}
                (colorizeCollection.{w, v, c} O.toCollection))).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection.{w, v, c} O.toCollection)).obj
              (ColoredSubstitutionData.oneColorFunctor.obj d)) := by
      with_unfolding_all exact
        (uncolorSourceNatIso (colorizeCollection.{w, v, c} O.toCollection)).hom.app d
    let source₂ :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection.{w, v, c} O.toCollection)).obj
              (ColoredSubstitutionData.oneColorFunctor.obj d)) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj d) := by
      with_unfolding_all
        exact ((colorizeSourceNatIso O.toCollection).hom.app
          (ColoredSubstitutionData.oneColorFunctor.obj d))
    let substO :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj d) ⟶
          O.toCollection.eval (substitutionTotalObj d) := O.subst.app d
    let substRound :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors
              (uncolorCollection (colorizeCollection O.toCollection))).obj d) ⟶
          O.toCollection.eval (substitutionTotalObj d) := by
      with_unfolding_all exact
        (uncolorObj.{w, v, c} (colorizeObj.{w, v, c} O)).subst.app d
    let targetMap :
        O.toCollection.eval (substitutionTotalObj d) ⟶
          O.toCollection.eval (substitutionTotalObj d) := by
      with_unfolding_all exact α.app ⟨substitutionTotalObj d⟩
    have hSource : sourceMap ≫ source₁ ≫ source₂ = 𝟙 _ :=
      ordinaryUnitSource_hom.{w, v, c} O.toCollection d
    have hRound : source₁ ≫ source₂ ≫ substO = substRound := by
      rfl
    have hTarget : targetMap = 𝟙 _ := ordinaryCollectionUnitIso_hom_app _ _
    have hComposite : sourceMap ≫ substRound = substO := by
      rw [← hRound]
      slice_lhs 1 3 => rw [hSource]
      simp
    change substO ≫ targetMap = sourceMap ≫ substRound
    rw [hTarget, Category.comp_id, hComposite]

/-- The inverse unit comparison as a morphism of ordinary operads. -/
noncomputable def ordinaryUnitInv (O : OperadObj V) :
    uncolorObj.{w, v, c} (colorizeObj.{w, v, c} O) ⟶ O where
  toCollectionHom := (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).inv
  map_unit := by
    let unitMap : O.toCollection.eval arityOne ⟶ O.toCollection.eval arityOne := by
      with_unfolding_all exact
        (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).inv.app ⟨arityOne⟩
    have hUnitMap : unitMap = 𝟙 _ := by rfl
    change O.unit ≫ unitMap = O.unit
    rw [hUnitMap, Category.comp_id]
  map_subst d := by
    let α := (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).inv
    let sourceMap :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors
              (uncolorCollection.{w, v, c}
                (colorizeCollection.{w, v, c} O.toCollection))).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj d) :=
      OperadObj.HomData.sourceHom α d
    let source₁ :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors
              (uncolorCollection.{w, v, c}
                (colorizeCollection.{w, v, c} O.toCollection))).obj d) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection.{w, v, c} O.toCollection)).obj
              (ColoredSubstitutionData.oneColorFunctor.obj d)) := by
      with_unfolding_all exact
        (uncolorSourceNatIso (colorizeCollection.{w, v, c} O.toCollection)).hom.app d
    let source₂ :
        (FiniteTensor.tensor (V := V)).obj
            ((ColoredOperadObj.substitutionFactors
              (colorizeCollection.{w, v, c} O.toCollection)).obj
              (ColoredSubstitutionData.oneColorFunctor.obj d)) ⟶
          (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj d) := by
      with_unfolding_all
        exact ((colorizeSourceNatIso O.toCollection).hom.app
          (ColoredSubstitutionData.oneColorFunctor.obj d))
    let substO :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors O.toCollection).obj d) ⟶
          O.toCollection.eval (substitutionTotalObj d) := O.subst.app d
    let substRound :
        (FiniteTensor.tensor (V := V)).obj
            ((Operad.substitutionFactors
              (uncolorCollection (colorizeCollection O.toCollection))).obj d) ⟶
          O.toCollection.eval (substitutionTotalObj d) := by
      with_unfolding_all exact
        (uncolorObj.{w, v, c} (colorizeObj.{w, v, c} O)).subst.app d
    let targetMap :
        O.toCollection.eval (substitutionTotalObj d) ⟶
          O.toCollection.eval (substitutionTotalObj d) := by
      with_unfolding_all exact α.app ⟨substitutionTotalObj d⟩
    have hSource : source₁ ≫ source₂ = sourceMap :=
      ordinaryUnitSource_inv.{w, v, c} O.toCollection d
    have hRound : source₁ ≫ source₂ ≫ substO = substRound := by
      rfl
    have hTarget : targetMap = 𝟙 _ := ordinaryCollectionUnitIso_inv_app _ _
    change substRound ≫ targetMap = sourceMap ≫ substO
    rw [hTarget, Category.comp_id]
    calc
      substRound = source₁ ≫ source₂ ≫ substO := hRound.symm
      _ = (source₁ ≫ source₂) ≫ substO := (Category.assoc _ _ _).symm
      _ = sourceMap ≫ substO := congrArg (fun f => f ≫ substO) hSource

/-- The ordinary operad recovered after colorization and forgetting is canonically isomorphic to
the original operad. -/
noncomputable def ordinaryUnitIso (O : OperadObj V) :
    O ≅ uncolorObj.{w, v, c} (colorizeObj.{w, v, c} O) where
  hom := ordinaryUnitHom.{w, v, c} O
  inv := ordinaryUnitInv.{w, v, c} O
  hom_inv_id := by
    apply OperadObj.Hom.ext
    exact (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).hom_inv_id
  inv_hom_id := by
    apply OperadObj.Hom.ext
    exact (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).inv_hom_id

/-- Unit natural isomorphism for the ordinary/one-colored operad equivalence. -/
noncomputable def ordinaryUnitIsoNat :
    𝟭 (OperadObj V) ≅ colorizeFunctor.{w, v, c} ⋙ uncolorFunctor.{w, v, c} :=
  NatIso.ofComponents (ordinaryUnitIso (V := V)) (by
    intro O P F
    apply OperadObj.Hom.ext
    apply NatTrans.ext
    funext I
    with_unfolding_all
      change F.toCollectionHom.app I ≫ 𝟙 _ = 𝟙 _ ≫ F.toCollectionHom.app I
      simp)

/-- A one-colored operad is canonically isomorphic to the operad obtained by forgetting and
then restoring its unique color. -/
noncomputable def coloredCounitIso (O : ColoredOperadObj PUnit V) :
    colorizeObj (uncolorObj O) ≅ O where
  hom := coloredCounitHom O
  inv := coloredCounitInv O
  hom_inv_id := by
    apply ColoredOperadObj.Hom.ext
    exact (coloredCollectionCounitIso O.toCollection).hom_inv_id
  inv_hom_id := by
    apply ColoredOperadObj.Hom.ext
    exact (coloredCollectionCounitIso O.toCollection).inv_hom_id

/-- Counit natural isomorphism for the ordinary/one-colored operad equivalence. -/
noncomputable def coloredCounitIsoNat :
    uncolorFunctor ⋙ colorizeFunctor ≅ 𝟭 (ColoredOperadObj PUnit V) :=
  NatIso.ofComponents (coloredCounitIso (V := V)) (by
    intro O P F
    have h :
        Functor.whiskerLeft ColoredProfile.forgetOneColorFunctor
              (Functor.whiskerLeft ColoredProfile.oneColorFunctor F.toCollectionHom) ≫
            (coloredCollectionCounitIso P.toCollection).hom =
          (coloredCollectionCounitIso O.toCollection).hom ≫ F.toCollectionHom := by
      apply NatTrans.ext
      funext Q
      with_unfolding_all
        change F.toCollectionHom.app _ ≫
              (coloredCollectionCounitIso P.toCollection).hom.app Q =
            (coloredCollectionCounitIso O.toCollection).hom.app Q ≫
              F.toCollectionHom.app Q
        rw [coloredCollectionCounitIso_hom_app, coloredCollectionCounitIso_hom_app]
        exact (F.toCollectionHom.naturality (ColoredProfile.oneColorCounitHom Q)).symm
    apply ColoredOperadObj.Hom.ext
    with_unfolding_all exact h)

/-- The chosen unit and counit for the one-color comparison satisfy the triangle identity. -/
theorem operadOneColor_triangle (O : OperadObj V) :
    (colorizeFunctor.{w, v, c} (V := V)).map
          ((ordinaryUnitIsoNat.{w, v, c} (V := V)).hom.app O) ≫
        (coloredCounitIsoNat.{w, v, c} (V := V)).hom.app
          ((colorizeFunctor.{w, v, c} (V := V)).obj O) =
      𝟙 _ := by
  apply ColoredOperadObj.Hom.ext
  apply NatTrans.ext
  funext P
  change
    (Functor.whiskerLeft ColoredProfile.forgetOneColorFunctor
          (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).hom).app P ≫
        (coloredCollectionCounitIso (colorizeCollection O.toCollection)).hom.app P =
      𝟙 ((colorizeCollection O.toCollection).obj P)
  rw [coloredCollectionCounitIso_hom_app]
  change (ordinaryCollectionUnitIso.{w, v, c} O.toCollection).hom.app
      (ColoredProfile.forgetOneColorFunctor.obj P) ≫
    (colorizeCollection O.toCollection).map (ColoredProfile.oneColorCounitHom P) = _
  rw [ordinaryCollectionUnitIso_hom_app]
  with_unfolding_all
    change 𝟙 _ ≫ O.toCollection.map
      (ColoredProfile.forgetOneColorFunctor.map (ColoredProfile.oneColorCounitHom P)) = 𝟙 _
  rw [Category.id_comp]
  rw [ColoredProfile.forgetOneColorFunctor_map_oneColorCounitHom]
  with_unfolding_all exact O.toCollection.map_id _

/-- Ordinary operads in `V` are categorically equivalent to `PUnit`-colored operads in `V`. -/
noncomputable def operadOneColorEquivalence :
    OperadObj V ≌ ColoredOperadObj PUnit V :=
  Equivalence.mk' colorizeFunctor uncolorFunctor ordinaryUnitIsoNat coloredCounitIsoNat
    operadOneColor_triangle

/-- The forward functor of the one-color equivalence is colorization. -/
@[simp]
theorem operadOneColorEquivalence_functor :
    (operadOneColorEquivalence (V := V)).functor = colorizeFunctor :=
  rfl

/-- The inverse functor of the one-color equivalence forgets the unique color. -/
@[simp]
theorem operadOneColorEquivalence_inverse :
    (operadOneColorEquivalence (V := V)).inverse = uncolorFunctor :=
  rfl

/-- The unit of the one-color equivalence is the chosen ordinary-operad comparison. -/
@[simp]
theorem operadOneColorEquivalence_unitIso :
    (operadOneColorEquivalence (V := V)).unitIso = ordinaryUnitIsoNat :=
  rfl

/-- The counit of the one-color equivalence is the chosen colored-operad comparison. -/
@[simp]
theorem operadOneColorEquivalence_counitIso :
    (operadOneColorEquivalence (V := V)).counitIso = coloredCounitIsoNat :=
  rfl

end CategoryTheory.Operad.ColoredOperadObj.OneColor

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
# Associativity compatibility for color-blind operads

The colored associativity routes for a color-blind collection agree with the ordinary routes after
the canonical comparisons of their nested finite families and common sources.
-/

@[expose] public section

namespace CategoryTheory.Operad.ColoredOperadObj.ColorBlind

open CategoryTheory

universe u v w

variable (Color : Type u)
variable {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- Compare the colored route-A grouping with the ordinary grouping after forgetting colors. -/
def groupingAIso (O : SymmetricCollection V) (d : ColoredAssocData Color) :
    ColoredOperadObj.AssocInsertion.groupingA (collection Color O) d ≅
      Operad.AssocInsertion.groupingA O (forgetColorsAssocData Color d) :=
  FiniteFamily.isoOfComponents (Equiv.refl _) (fun
    | none => Iso.refl _
    | some i => factorIso Color O (d.localData i))

/-- Forward map of `groupingAIso`. -/
abbrev groupingAHom (O : SymmetricCollection V) (d : ColoredAssocData Color) :=
  (groupingAIso Color O d).hom

/-- Compare the colored route-B grouping with the ordinary grouping after forgetting colors. -/
def groupingBIso (O : SymmetricCollection V) (d : ColoredAssocData Color) :
    ColoredOperadObj.AssocInsertion.groupingB (collection Color O) d ≅
      Operad.AssocInsertion.groupingB O (forgetColorsAssocData Color d) :=
  FiniteFamily.isoOfComponents (Equiv.refl _) (fun
    | none => factorIso Color O d.middleData
    | some _ => Iso.refl _)

/-- Forward map of `groupingBIso`. -/
abbrev groupingBHom (O : SymmetricCollection V) (d : ColoredAssocData Color) :=
  (groupingBIso Color O d).hom

/-- The route-A grouping comparison after flattening its nested finite family. -/
def flattenedGroupingAIso (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    ColoredOperadObj.AssocInsertion.flattenedGroupingA (collection Color O) d ≅
      Operad.AssocInsertion.flattenedGroupingA O (forgetColorsAssocData Color d) :=
  FiniteFamily.flatten.mapIso (groupingAIso Color O d)

/-- The route-B grouping comparison after flattening its nested finite family. -/
def flattenedGroupingBIso (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    ColoredOperadObj.AssocInsertion.flattenedGroupingB (collection Color O) d ≅
      Operad.AssocInsertion.flattenedGroupingB O (forgetColorsAssocData Color d) :=
  FiniteFamily.flatten.mapIso (groupingBIso Color O d)

/-- Comparison between the common sources of colored and ordinary associativity routes. -/
def assocSourceIso (O : SymmetricCollection V) (d : ColoredAssocData Color) :
    ColoredOperadObj.associativityCommonSource (collection Color O) d ≅
      Operad.associativityCommonSource O (forgetColorsAssocData Color d) :=
  (FiniteTensor.tensor (V := V)).mapIso (flattenedGroupingAIso Color O d)

/-- Route-A factor assembly commutes with the color-blind comparison. -/
theorem groupingAToFactors_compat (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map (groupingAHom Color O d) ≫
        Operad.AssocInsertion.groupingAToFactorsHom O γ (forgetColorsAssocData Color d) =
      ColoredOperadObj.AssocInsertion.groupingAToFactorsHom
          (collection Color O) (substitutionData Color O γ) d ≫
        factorHom Color O d.outerAfterInnerData := by
  let lhs := (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
      (groupingAHom Color O d) ≫
    Operad.AssocInsertion.groupingAToFactorsHom O γ (forgetColorsAssocData Color d)
  let rhs := ColoredOperadObj.AssocInsertion.groupingAToFactorsHom
      (collection Color O) (substitutionData Color O γ) d ≫
    factorHom Color O d.outerAfterInnerData
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        let a := (FiniteTensor.singletonIso (V := V)).hom.app
          (O.obj ⟨d.branches.index⟩)
        have hLeft : HEq (lhs.hom none) a := by
          with_unfolding_all
            exact heq_of_eq ((show lhs.hom none =
              (FiniteTensor.tensor (V := V)).map (𝟙 _) ≫ a from rfl).trans (by
                rw [(FiniteTensor.tensor (V := V)).map_id, Category.id_comp]))
        have hRight : HEq a (rhs.hom none) := by
          have h0 : HEq (rhs.hom none) (a ≫ 𝟙 _) := by
            with_unfolding_all exact heq_of_eq rfl
          have h1 : HEq (a ≫ 𝟙 _) a := heq_of_eq (Category.comp_id _)
          exact (h0.trans h1).symm
        exact hLeft.trans hRight
    | some i =>
        let a := (FiniteTensor.tensor (V := V)).map
          (factorHom Color O (d.localData i))
        let b := γ.app (ColoredSubstitutionData.toSubstitutionDataFunctor.obj (d.localData i))
        have hLeft : HEq (lhs.hom (some i)) (a ≫ b) := by
          with_unfolding_all exact heq_of_eq rfl
        have hRight : HEq (a ≫ b) (rhs.hom (some i)) := by
          have h0 : HEq (rhs.hom (some i)) ((a ≫ b) ≫ 𝟙 _) := by
            with_unfolding_all exact heq_of_eq rfl
          have h1 : HEq ((a ≫ b) ≫ 𝟙 _) (a ≫ b) :=
            heq_of_eq (Category.comp_id _)
          exact (h0.trans h1).symm
        exact hLeft.trans hRight

/-- Route-B factor assembly commutes with the color-blind comparison. -/
theorem groupingBToFactors_compat (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map (groupingBHom Color O d) ≫
        Operad.AssocInsertion.groupingBToFactorsHom O γ (forgetColorsAssocData Color d) =
      ColoredOperadObj.AssocInsertion.groupingBToFactorsHom
          (collection Color O) (substitutionData Color O γ) d ≫
        factorHom Color O d.innerData := by
  let lhs := (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
      (groupingBHom Color O d) ≫
    Operad.AssocInsertion.groupingBToFactorsHom O γ (forgetColorsAssocData Color d)
  let rhs := ColoredOperadObj.AssocInsertion.groupingBToFactorsHom
      (collection Color O) (substitutionData Color O γ) d ≫
    factorHom Color O d.innerData
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        let a := (FiniteTensor.tensor (V := V)).map (factorHom Color O d.middleData)
        let b := γ.app (ColoredSubstitutionData.toSubstitutionDataFunctor.obj d.middleData)
        have hLeft : HEq (lhs.hom none) (a ≫ b) := by
          with_unfolding_all exact heq_of_eq rfl
        have hRight : HEq (a ≫ b) (rhs.hom none) := by
          have h0 : HEq (rhs.hom none) ((a ≫ b) ≫ 𝟙 _) := by
            with_unfolding_all exact heq_of_eq rfl
          have h1 : HEq ((a ≫ b) ≫ 𝟙 _) (a ≫ b) :=
            heq_of_eq (Category.comp_id _)
          exact (h0.trans h1).symm
        exact hLeft.trans hRight
    | some p =>
        let a := (FiniteTensor.singletonIso (V := V)).hom.app
          (O.obj ⟨((d.localData p.1).inner.obj p.2).inputs⟩)
        have hLeft : HEq (lhs.hom (some p)) a := by
          with_unfolding_all
            exact heq_of_eq ((show lhs.hom (some p) =
              (FiniteTensor.tensor (V := V)).map (𝟙 _) ≫ a from rfl).trans (by
                rw [(FiniteTensor.tensor (V := V)).map_id, Category.id_comp]))
        have hRight : HEq a (rhs.hom (some p)) := by
          have h0 : HEq (rhs.hom (some p)) (a ≫ 𝟙 _) := by
            with_unfolding_all exact heq_of_eq rfl
          have h1 : HEq (a ≫ 𝟙 _) a := heq_of_eq (Category.comp_id _)
          exact (h0.trans h1).symm
        exact hLeft.trans hRight

omit [FiniteTensor V] in
/-- Rebracketing from flattened route A to route B commutes with the color-blind comparison. -/
theorem flattenAToFlattenB_compat (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    (flattenedGroupingAIso Color O d).hom ≫
        Operad.AssocInsertion.flattenAToFlattenBHom O (forgetColorsAssocData Color d) =
      ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom
          (collection Color O) d ≫
        (flattenedGroupingBIso Color O d).hom := by
  let lhs := (flattenedGroupingAIso Color O d).hom ≫
    Operad.AssocInsertion.flattenAToFlattenBHom O (forgetColorsAssocData Color d)
  let rhs := ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom
      (collection Color O) d ≫
    (flattenedGroupingBIso Color O d).hom
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro x
    rcases x with ⟨o, a⟩
    cases o with
    | none => cases a; rfl
    | some i => cases a <;> rfl
  · intro x
    rcases x with ⟨o, a⟩
    cases o with
    | none =>
        cases a
        with_unfolding_all
          change HEq ((𝟙 _) ≫ (𝟙 _)) ((𝟙 _) ≫ (𝟙 _))
          exact heq_of_eq rfl
    | some i =>
        cases a with
        | none =>
            with_unfolding_all
              change HEq ((𝟙 _) ≫ (𝟙 _)) ((𝟙 _) ≫ (𝟙 _))
              exact heq_of_eq rfl
        | some j =>
            with_unfolding_all
              change HEq ((𝟙 _) ≫ (𝟙 _)) ((𝟙 _) ≫ (𝟙 _))
              exact heq_of_eq rfl

/-- Component formula for the color-blind associativity-source comparison. -/
@[simp]
theorem assocSourceIso_hom (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    (assocSourceIso Color O d).hom =
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.flatten (C := V)).map (groupingAHom Color O d)) :=
  rfl

/-- Ordinary associativity route A agrees with its color-blind counterpart. -/
theorem associativityRouteA_compat (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : ColoredAssocData Color) :
    (assocSourceIso Color O d).hom ≫
        Operad.associativityRouteA O γ (forgetColorsAssocData Color d) =
      ColoredOperadObj.associativityRouteA
      (collection Color O) (substitutionData Color O γ) d := by
  let groupHom := groupingAHom Color O d
  let flatHom := (FiniteFamily.flatten (C := V)).map groupHom
  let mappedGroupHom :=
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map groupHom
  let groupOrd :=
    Operad.AssocInsertion.groupingAToFactorsHom O γ (forgetColorsAssocData Color d)
  let groupCol :=
    ColoredOperadObj.AssocInsertion.groupingAToFactorsHom
      (collection Color O) (substitutionData Color O γ) d
  let factor :
      (ColoredOperadObj.substitutionFactors (collection Color O)).obj
          d.outerAfterInnerData ⟶
        (Operad.substitutionFactors O).obj (forgetColorsAssocData Color d).outerAfterInnerData := by
    with_unfolding_all exact factorHom Color O d.outerAfterInnerData
  let outerOrd :
      (FiniteTensor.tensor (V := V)).obj
          ((Operad.substitutionFactors O).obj (forgetColorsAssocData Color d).outerAfterInnerData) ⟶
        O.eval (substitutionTotalObj (forgetColorsAssocData Color d).outerAfterInnerData) :=
    γ.app (forgetColorsAssocData Color d).outerAfterInnerData
  let outerCol :
      (FiniteTensor.tensor (V := V)).obj
          ((ColoredOperadObj.substitutionFactors (collection Color O)).obj
            d.outerAfterInnerData) ⟶
        O.eval (substitutionTotalObj (forgetColorsAssocData Color d).outerAfterInnerData) := by
    with_unfolding_all exact (substitutionData Color O γ).app d.outerAfterInnerData
  have hGroup : mappedGroupHom ≫ groupOrd = groupCol ≫ factor := by
    with_unfolding_all exact groupingAToFactors_compat Color O γ d
  have hFlatten :
      (FiniteTensor.tensor (V := V)).map flatHom ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (Operad.AssocInsertion.groupingA O (forgetColorsAssocData Color d)) =
      (FiniteTensor.flattenIso (V := V)).hom.app
          (ColoredOperadObj.AssocInsertion.groupingA (collection Color O) d) ≫
        (FiniteTensor.tensor (V := V)).map mappedGroupHom := by
    with_unfolding_all
      exact (FiniteTensor.flattenIso (V := V)).hom.naturality
        (groupingAHom Color O d)
  have hGroupTensor :
      (FiniteTensor.tensor (V := V)).map mappedGroupHom ≫
          (FiniteTensor.tensor (V := V)).map groupOrd =
        (FiniteTensor.tensor (V := V)).map groupCol ≫
          (FiniteTensor.tensor (V := V)).map factor := by
    calc
      _ = (FiniteTensor.tensor (V := V)).map (mappedGroupHom ≫ groupOrd) :=
        ((FiniteTensor.tensor (V := V)).map_comp mappedGroupHom groupOrd).symm
      _ = (FiniteTensor.tensor (V := V)).map (groupCol ≫ factor) :=
        congrArg (fun f => (FiniteTensor.tensor (V := V)).map f) hGroup
      _ = _ := (FiniteTensor.tensor (V := V)).map_comp groupCol factor
  have hOuter : (FiniteTensor.tensor (V := V)).map factor ≫ outerOrd = outerCol := by
    rfl
  change (FiniteTensor.tensor (V := V)).map flatHom ≫
      ((FiniteTensor.flattenIso (V := V)).hom.app
          (Operad.AssocInsertion.groupingA O (forgetColorsAssocData Color d)) ≫
        (FiniteTensor.tensor (V := V)).map groupOrd ≫
        outerOrd) =
    (FiniteTensor.flattenIso (V := V)).hom.app
        (ColoredOperadObj.AssocInsertion.groupingA (collection Color O) d) ≫
      (FiniteTensor.tensor (V := V)).map groupCol ≫
      outerCol
  slice_lhs 1 2 => rw [hFlatten]
  slice_lhs 2 3 => rw [hGroupTensor]
  slice_lhs 3 4 => rw [hOuter]

omit [FiniteTensor V] in
/-- The color-blind lift identifies the colored associativity relabelling with the ordinary one. -/
@[simp]
theorem collection_map_totalHom (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    (collection Color O).map d.totalHom =
      O.relabelIso (forgetColorsAssocData Color d).totalIso := by
  rfl

/-- Ordinary associativity route B agrees with its color-blind counterpart. -/
theorem associativityRouteB_compat (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : ColoredAssocData Color) :
    (assocSourceIso Color O d).hom ≫
        Operad.associativityRouteB O γ (forgetColorsAssocData Color d) =
      ColoredOperadObj.associativityRouteB
        (collection Color O) (substitutionData Color O γ) d := by
  let groupAHom := groupingAHom Color O d
  let groupBHom := groupingBHom Color O d
  let flatAHom := (FiniteFamily.flatten (C := V)).map groupAHom
  let flatBHom := (FiniteFamily.flatten (C := V)).map groupBHom
  let flattenOrd :
      (FiniteFamily.flatten (C := V)).obj
          (Operad.AssocInsertion.groupingA O (forgetColorsAssocData Color d)) ⟶
        (FiniteFamily.flatten (C := V)).obj
          (Operad.AssocInsertion.groupingB O (forgetColorsAssocData Color d)) := by
    with_unfolding_all
      exact Operad.AssocInsertion.flattenAToFlattenBHom O (forgetColorsAssocData Color d)
  let flattenCol :
      (FiniteFamily.flatten (C := V)).obj
          (ColoredOperadObj.AssocInsertion.groupingA (collection Color O) d) ⟶
        (FiniteFamily.flatten (C := V)).obj
          (ColoredOperadObj.AssocInsertion.groupingB (collection Color O) d) := by
    with_unfolding_all
      exact ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom
        (collection Color O) d
  let mappedGroupBHom :=
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map groupBHom
  let groupOrd :=
    Operad.AssocInsertion.groupingBToFactorsHom O γ (forgetColorsAssocData Color d)
  let groupCol :=
    ColoredOperadObj.AssocInsertion.groupingBToFactorsHom
      (collection Color O) (substitutionData Color O γ) d
  let factor :
      (ColoredOperadObj.substitutionFactors (collection Color O)).obj d.innerData ⟶
        (Operad.substitutionFactors O).obj (forgetColorsAssocData Color d).innerData := by
    with_unfolding_all exact factorHom Color O d.innerData
  let innerOrd :
      (FiniteTensor.tensor (V := V)).obj
          ((Operad.substitutionFactors O).obj (forgetColorsAssocData Color d).innerData) ⟶
        O.eval (substitutionTotalObj (forgetColorsAssocData Color d).innerData) :=
    γ.app (forgetColorsAssocData Color d).innerData
  let innerCol :
      (FiniteTensor.tensor (V := V)).obj
          ((ColoredOperadObj.substitutionFactors (collection Color O)).obj d.innerData) ⟶
        O.eval (substitutionTotalObj (forgetColorsAssocData Color d).innerData) := by
    with_unfolding_all exact (substitutionData Color O γ).app d.innerData
  let relabelOrd :
      O.eval (substitutionTotalObj (forgetColorsAssocData Color d).innerData) ⟶
        O.eval (substitutionTotalObj (forgetColorsAssocData Color d).outerAfterInnerData) :=
    O.relabelIso (forgetColorsAssocData Color d).totalIso
  let relabelCol :
      O.eval (substitutionTotalObj (forgetColorsAssocData Color d).innerData) ⟶
        O.eval (substitutionTotalObj (forgetColorsAssocData Color d).outerAfterInnerData) := by
    with_unfolding_all exact (collection Color O).map d.totalHom
  have hFlat : flatAHom ≫ flattenOrd = flattenCol ≫ flatBHom := by
    with_unfolding_all exact flattenAToFlattenB_compat Color O d
  have hFlatTensor :
      (FiniteTensor.tensor (V := V)).map flatAHom ≫
          (FiniteTensor.tensor (V := V)).map flattenOrd =
        (FiniteTensor.tensor (V := V)).map flattenCol ≫
          (FiniteTensor.tensor (V := V)).map flatBHom := by
    calc
      _ = (FiniteTensor.tensor (V := V)).map (flatAHom ≫ flattenOrd) :=
        ((FiniteTensor.tensor (V := V)).map_comp flatAHom flattenOrd).symm
      _ = (FiniteTensor.tensor (V := V)).map (flattenCol ≫ flatBHom) :=
        congrArg (fun f => (FiniteTensor.tensor (V := V)).map f) hFlat
      _ = _ := (FiniteTensor.tensor (V := V)).map_comp flattenCol flatBHom
  have hFlattenB :
      (FiniteTensor.tensor (V := V)).map flatBHom ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (Operad.AssocInsertion.groupingB O (forgetColorsAssocData Color d)) =
      (FiniteTensor.flattenIso (V := V)).hom.app
        (ColoredOperadObj.AssocInsertion.groupingB (collection Color O) d) ≫
        (FiniteTensor.tensor (V := V)).map mappedGroupBHom := by
    with_unfolding_all
      exact (FiniteTensor.flattenIso (V := V)).hom.naturality groupBHom
  have hGroup : mappedGroupBHom ≫ groupOrd = groupCol ≫ factor := by
    with_unfolding_all exact groupingBToFactors_compat Color O γ d
  have hGroupTensor :
      (FiniteTensor.tensor (V := V)).map mappedGroupBHom ≫
          (FiniteTensor.tensor (V := V)).map groupOrd =
        (FiniteTensor.tensor (V := V)).map groupCol ≫
          (FiniteTensor.tensor (V := V)).map factor := by
    calc
      _ = (FiniteTensor.tensor (V := V)).map (mappedGroupBHom ≫ groupOrd) :=
        ((FiniteTensor.tensor (V := V)).map_comp mappedGroupBHom groupOrd).symm
      _ = (FiniteTensor.tensor (V := V)).map (groupCol ≫ factor) :=
        congrArg (fun f => (FiniteTensor.tensor (V := V)).map f) hGroup
      _ = _ := (FiniteTensor.tensor (V := V)).map_comp groupCol factor
  have hInner :
      (FiniteTensor.tensor (V := V)).map factor ≫ innerOrd = innerCol := by
    rfl
  have hRelabel : relabelOrd = relabelCol := by
    rfl
  change (FiniteTensor.tensor (V := V)).map flatAHom ≫
      ((FiniteTensor.tensor (V := V)).map flattenOrd ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (Operad.AssocInsertion.groupingB O (forgetColorsAssocData Color d)) ≫
        (FiniteTensor.tensor (V := V)).map groupOrd ≫ innerOrd ≫ relabelOrd) =
    (FiniteTensor.tensor (V := V)).map flattenCol ≫
      (FiniteTensor.flattenIso (V := V)).hom.app
        (ColoredOperadObj.AssocInsertion.groupingB (collection Color O) d) ≫
      (FiniteTensor.tensor (V := V)).map groupCol ≫ innerCol ≫ relabelCol
  slice_lhs 1 2 => rw [hFlatTensor]
  slice_lhs 2 3 => rw [hFlattenB]
  slice_lhs 3 4 => rw [hGroupTensor]
  slice_lhs 4 5 => rw [hInner]
  rw [hRelabel]

end CategoryTheory.Operad.ColoredOperadObj.ColorBlind

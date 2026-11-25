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
public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.OneColorData

/-!
# One-color compatibility of operadic associativity

The two associativity routes for ordinary and one-colored operads agree through canonical
isomorphisms of their nested factor families. This is the associativity-law regression layer for
the equivalence between ordinary operads and operads with color type PUnit.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Operad.ColoredOperadObj.OneColor

universe w v

variable {V : Type w} [Category.{v} V] [FiniteTensor V]


/-- Compare the route-A grouping families after colorizing an ordinary collection. -/
abbrev colorizeGroupingAIso (O : SymmetricCollection V) (d : ColoredAssocData PUnit) :=
  ColoredOperadObj.ColorBlind.groupingAIso PUnit O d

/-- Forward map of `colorizeGroupingAIso`. -/
abbrev colorizeGroupingAHom (O : SymmetricCollection V) (d : ColoredAssocData PUnit) :=
  ColoredOperadObj.ColorBlind.groupingAHom PUnit O d

/-- Compare the route-B grouping families after colorizing an ordinary collection. -/
abbrev colorizeGroupingBIso (O : SymmetricCollection V) (d : ColoredAssocData PUnit) :=
  ColoredOperadObj.ColorBlind.groupingBIso PUnit O d

/-- Forward map of `colorizeGroupingBIso`. -/
abbrev colorizeGroupingBHom (O : SymmetricCollection V) (d : ColoredAssocData PUnit) :=
  ColoredOperadObj.ColorBlind.groupingBHom PUnit O d

/-- The route-A grouping comparison after flattening its nested finite family. -/
abbrev colorizeFlattenedGroupingAIso (O : SymmetricCollection V)
    (d : ColoredAssocData PUnit) :=
  ColoredOperadObj.ColorBlind.flattenedGroupingAIso PUnit O d

/-- The route-B grouping comparison after flattening its nested finite family. -/
abbrev colorizeFlattenedGroupingBIso (O : SymmetricCollection V)
    (d : ColoredAssocData PUnit) :=
  ColoredOperadObj.ColorBlind.flattenedGroupingBIso PUnit O d

/-- Comparison between the common sources of colored and ordinary associativity routes. -/
abbrev colorizeAssocSourceIso (O : SymmetricCollection V) (d : ColoredAssocData PUnit) :=
  ColoredOperadObj.ColorBlind.assocSourceIso PUnit O d

/-- Route-A factor assembly commutes with colorization. -/
theorem colorizeGroupingAToFactors_compat (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : ColoredAssocData PUnit) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map (colorizeGroupingAHom O d) ≫
        Operad.AssocInsertion.groupingAToFactorsHom O γ (uncolorAssocData d) =
      ColoredOperadObj.AssocInsertion.groupingAToFactorsHom
          (colorizeCollection O) (colorizeSubst O γ) d ≫
        colorizeFactorHom O d.outerAfterInnerData :=
  ColoredOperadObj.ColorBlind.groupingAToFactors_compat PUnit O γ d

/-- Route-B factor assembly commutes with colorization. -/
theorem colorizeGroupingBToFactors_compat (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : ColoredAssocData PUnit) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map (colorizeGroupingBHom O d) ≫
        Operad.AssocInsertion.groupingBToFactorsHom O γ (uncolorAssocData d) =
      ColoredOperadObj.AssocInsertion.groupingBToFactorsHom
          (colorizeCollection O) (colorizeSubst O γ) d ≫
        colorizeFactorHom O d.innerData :=
  ColoredOperadObj.ColorBlind.groupingBToFactors_compat PUnit O γ d

omit [FiniteTensor V] in
/-- Rebracketing from flattened route A to route B commutes with colorization. -/
theorem colorizeFlattenAToFlattenB_compat (O : SymmetricCollection V)
    (d : ColoredAssocData PUnit) :
    (colorizeFlattenedGroupingAIso O d).hom ≫
        Operad.AssocInsertion.flattenAToFlattenBHom O (uncolorAssocData d) =
      ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom
          (colorizeCollection O) d ≫
        (colorizeFlattenedGroupingBIso O d).hom :=
  ColoredOperadObj.ColorBlind.flattenAToFlattenB_compat PUnit O d

/-- Component formula for the colorized associativity-source comparison. -/
@[simp]
theorem colorizeAssocSourceIso_hom (O : SymmetricCollection V)
    (d : ColoredAssocData PUnit) :
    (colorizeAssocSourceIso O d).hom =
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.flatten (C := V)).map (colorizeGroupingAHom O d)) :=
  rfl

/-- Ordinary associativity route A agrees with its colorized counterpart. -/
theorem colorizeAssociativityRouteA_compat (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : ColoredAssocData PUnit) :
    (colorizeAssocSourceIso O d).hom ≫
        Operad.associativityRouteA O γ (uncolorAssocData d) =
      ColoredOperadObj.associativityRouteA
        (colorizeCollection O) (colorizeSubst O γ) d :=
  ColoredOperadObj.ColorBlind.associativityRouteA_compat PUnit O γ d

omit [FiniteTensor V] in
/-- Colorization identifies the colored associativity relabelling with the ordinary one. -/
@[simp]
theorem colorizeCollection_map_totalHom (O : SymmetricCollection V)
    (d : ColoredAssocData PUnit) :
    (colorizeCollection O).map d.totalHom =
      O.relabelIso (uncolorAssocData d).totalIso :=
  ColoredOperadObj.ColorBlind.collection_map_totalHom PUnit O d

/-- Ordinary associativity route B agrees with its colorized counterpart. -/
theorem colorizeAssociativityRouteB_compat (O : SymmetricCollection V)
    (γ : OperadSubstitution O) (d : ColoredAssocData PUnit) :
    (colorizeAssocSourceIso O d).hom ≫
        Operad.associativityRouteB O γ (uncolorAssocData d) =
      ColoredOperadObj.associativityRouteB
        (colorizeCollection O) (colorizeSubst O γ) d :=
  ColoredOperadObj.ColorBlind.associativityRouteB_compat PUnit O γ d

/-- Compare the route-A grouping families after forgetting a one-colored collection. -/
def uncolorGroupingAIso (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :
    Operad.AssocInsertion.groupingA (uncolorCollection O) d ≅
      ColoredOperadObj.AssocInsertion.groupingA O (colorizeAssocData d) :=
  FiniteFamily.isoOfComponents (Equiv.refl _) (fun
    | none => Iso.refl _
    | some i => uncolorFactorIso O (d.localData i))

/-- Forward map of `uncolorGroupingAIso`. -/
abbrev uncolorGroupingAHom (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :=
  (uncolorGroupingAIso O d).hom

/-- Compare the route-B grouping families after forgetting a one-colored collection. -/
def uncolorGroupingBIso (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :
    Operad.AssocInsertion.groupingB (uncolorCollection O) d ≅
      ColoredOperadObj.AssocInsertion.groupingB O (colorizeAssocData d) :=
  FiniteFamily.isoOfComponents (Equiv.refl _) (fun
    | none => uncolorFactorIso O d.middleData
    | some _ => Iso.refl _)

/-- Forward map of `uncolorGroupingBIso`. -/
abbrev uncolorGroupingBHom (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :=
  (uncolorGroupingBIso O d).hom

/-- The route-A grouping comparison after flattening and forgetting the unique color. -/
def uncolorFlattenedGroupingAIso (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :
    Operad.AssocInsertion.flattenedGroupingA (uncolorCollection O) d ≅
      ColoredOperadObj.AssocInsertion.flattenedGroupingA O (colorizeAssocData d) :=
  FiniteFamily.flatten.mapIso (uncolorGroupingAIso O d)

/-- The route-B grouping comparison after flattening and forgetting the unique color. -/
def uncolorFlattenedGroupingBIso (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :
    Operad.AssocInsertion.flattenedGroupingB (uncolorCollection O) d ≅
      ColoredOperadObj.AssocInsertion.flattenedGroupingB O (colorizeAssocData d) :=
  FiniteFamily.flatten.mapIso (uncolorGroupingBIso O d)

/-- Comparison between the ordinary and colored common associativity sources. -/
def uncolorAssocSourceIso (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :
    Operad.associativityCommonSource (uncolorCollection O) d ≅
      ColoredOperadObj.associativityCommonSource O (colorizeAssocData d) :=
  (FiniteTensor.tensor (V := V)).mapIso (uncolorFlattenedGroupingAIso O d)

/-- Component formula for the associativity-source comparison after forgetting one color. -/
@[simp]
theorem uncolorAssocSourceIso_hom (O : ColoredSymmetricCollection PUnit V)
    (d : AssocData) :
    (uncolorAssocSourceIso O d).hom =
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.flatten (C := V)).map (uncolorGroupingAHom O d)) :=
  rfl

/-- Route-A factor assembly commutes with forgetting the unique color. -/
theorem uncolorGroupingAToFactors_compat (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : AssocData) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map (uncolorGroupingAHom O d) ≫
        ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O γ (colorizeAssocData d) =
      Operad.AssocInsertion.groupingAToFactorsHom
          (uncolorCollection O) (uncolorSubst O γ) d ≫
        uncolorFactorHom O d.outerAfterInnerData := by
  let lhs := (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
      (uncolorGroupingAHom O d) ≫
    ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O γ (colorizeAssocData d)
  let rhs := Operad.AssocInsertion.groupingAToFactorsHom
      (uncolorCollection O) (uncolorSubst O γ) d ≫
    uncolorFactorHom O d.outerAfterInnerData
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        let a := (FiniteTensor.singletonIso (V := V)).hom.app
          (O.obj (ColoredProfile.oneColorFunctor.obj ⟨d.outer⟩))
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
          (uncolorFactorHom O (d.localData i))
        let b := γ.app (ColoredSubstitutionData.oneColorFunctor.obj (d.localData i))
        have hLeft : HEq (lhs.hom (some i)) (a ≫ b) := by
          with_unfolding_all exact heq_of_eq rfl
        have hRight : HEq (a ≫ b) (rhs.hom (some i)) := by
          have h0 : HEq (rhs.hom (some i)) ((a ≫ b) ≫ 𝟙 _) := by
            with_unfolding_all exact heq_of_eq rfl
          have h1 : HEq ((a ≫ b) ≫ 𝟙 _) (a ≫ b) :=
            heq_of_eq (Category.comp_id _)
          exact (h0.trans h1).symm
        exact hLeft.trans hRight

/-- Route-B factor assembly commutes with forgetting the unique color. -/
theorem uncolorGroupingBToFactors_compat (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : AssocData) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map (uncolorGroupingBHom O d) ≫
        ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O γ (colorizeAssocData d) =
      Operad.AssocInsertion.groupingBToFactorsHom
          (uncolorCollection O) (uncolorSubst O γ) d ≫
        uncolorFactorHom O d.innerData := by
  let lhs := (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
      (uncolorGroupingBHom O d) ≫
    ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O γ (colorizeAssocData d)
  let rhs := Operad.AssocInsertion.groupingBToFactorsHom
      (uncolorCollection O) (uncolorSubst O γ) d ≫
    uncolorFactorHom O d.innerData
  with_unfolding_all change lhs = rhs
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
        let a := (FiniteTensor.tensor (V := V)).map (uncolorFactorHom O d.middleData)
        let b := γ.app (ColoredSubstitutionData.oneColorFunctor.obj d.middleData)
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
          (O.obj (ColoredProfile.oneColorFunctor.obj ⟨d.inner p⟩))
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
/-- Rebracketing from flattened route A to route B commutes with forgetting one color. -/
theorem uncolorFlattenAToFlattenB_compat (O : ColoredSymmetricCollection PUnit V)
    (d : AssocData) :
    (uncolorFlattenedGroupingAIso O d).hom ≫
        ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O (colorizeAssocData d) =
      Operad.AssocInsertion.flattenAToFlattenBHom (uncolorCollection O) d ≫
        (uncolorFlattenedGroupingBIso O d).hom := by
  let lhs := (uncolorFlattenedGroupingAIso O d).hom ≫
    ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O (colorizeAssocData d)
  let rhs := Operad.AssocInsertion.flattenAToFlattenBHom (uncolorCollection O) d ≫
    (uncolorFlattenedGroupingBIso O d).hom
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

/-- Colored associativity route A agrees with its ordinary one-color counterpart. -/
theorem uncolorAssociativityRouteA_compat (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : AssocData) :
    (uncolorAssocSourceIso O d).hom ≫
        ColoredOperadObj.associativityRouteA O γ (colorizeAssocData d) =
      Operad.associativityRouteA (uncolorCollection O) (uncolorSubst O γ) d := by
  let groupHom := uncolorGroupingAHom O d
  let flatHom := (FiniteFamily.flatten (C := V)).map groupHom
  let mappedGroupHom :=
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map groupHom
  let groupCol :=
    ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O γ (colorizeAssocData d)
  let groupOrd :=
    Operad.AssocInsertion.groupingAToFactorsHom
      (uncolorCollection O) (uncolorSubst O γ) d
  let factor :
      (Operad.substitutionFactors (uncolorCollection O)).obj d.outerAfterInnerData ⟶
        (ColoredOperadObj.substitutionFactors O).obj
          (colorizeAssocData d).outerAfterInnerData := by
    with_unfolding_all exact uncolorFactorHom O d.outerAfterInnerData
  let outerCol :
      (FiniteTensor.tensor (V := V)).obj
          ((ColoredOperadObj.substitutionFactors O).obj
            (colorizeAssocData d).outerAfterInnerData) ⟶
        O.obj (colorizeAssocData d).outerAfterInnerData.totalProfile :=
    γ.app (colorizeAssocData d).outerAfterInnerData
  let outerOrd :
      (FiniteTensor.tensor (V := V)).obj
          ((Operad.substitutionFactors (uncolorCollection O)).obj d.outerAfterInnerData) ⟶
        O.obj (colorizeAssocData d).outerAfterInnerData.totalProfile := by
    with_unfolding_all exact (uncolorSubst O γ).app d.outerAfterInnerData
  have hGroup : mappedGroupHom ≫ groupCol = groupOrd ≫ factor := by
    with_unfolding_all exact uncolorGroupingAToFactors_compat O γ d
  have hFlatten :
      (FiniteTensor.tensor (V := V)).map flatHom ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (ColoredOperadObj.AssocInsertion.groupingA O (colorizeAssocData d)) =
      (FiniteTensor.flattenIso (V := V)).hom.app
          (Operad.AssocInsertion.groupingA (uncolorCollection O) d) ≫
        (FiniteTensor.tensor (V := V)).map mappedGroupHom := by
    with_unfolding_all
      exact (FiniteTensor.flattenIso (V := V)).hom.naturality groupHom
  have hGroupTensor :
      (FiniteTensor.tensor (V := V)).map mappedGroupHom ≫
          (FiniteTensor.tensor (V := V)).map groupCol =
        (FiniteTensor.tensor (V := V)).map groupOrd ≫
          (FiniteTensor.tensor (V := V)).map factor := by
    calc
      _ = (FiniteTensor.tensor (V := V)).map (mappedGroupHom ≫ groupCol) :=
        ((FiniteTensor.tensor (V := V)).map_comp mappedGroupHom groupCol).symm
      _ = (FiniteTensor.tensor (V := V)).map (groupOrd ≫ factor) :=
        congrArg (fun f => (FiniteTensor.tensor (V := V)).map f) hGroup
      _ = _ := (FiniteTensor.tensor (V := V)).map_comp groupOrd factor
  have hOuter :
      (FiniteTensor.tensor (V := V)).map factor ≫ outerCol = outerOrd := by
    rfl
  change (FiniteTensor.tensor (V := V)).map flatHom ≫
      ((FiniteTensor.flattenIso (V := V)).hom.app
          (ColoredOperadObj.AssocInsertion.groupingA O (colorizeAssocData d)) ≫
        (FiniteTensor.tensor (V := V)).map groupCol ≫
        outerCol) =
    (FiniteTensor.flattenIso (V := V)).hom.app
        (Operad.AssocInsertion.groupingA (uncolorCollection O) d) ≫
      (FiniteTensor.tensor (V := V)).map groupOrd ≫
      outerOrd
  slice_lhs 1 2 => rw [hFlatten]
  slice_lhs 2 3 => rw [hGroupTensor]
  slice_lhs 3 4 => rw [hOuter]

omit [FiniteTensor V] in
/-- Forgetting one color identifies the ordinary associativity relabelling with the colored one. -/
@[simp]
theorem uncolorCollection_relabelIso_totalIso
    (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :
    (uncolorCollection O).relabelIso d.totalIso =
      O.map (colorizeAssocData d).totalHom := by
  rfl

/-- Colored associativity route B agrees with its ordinary one-color counterpart. -/
theorem uncolorAssociativityRouteB_compat (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : AssocData) :
    (uncolorAssocSourceIso O d).hom ≫
        ColoredOperadObj.associativityRouteB O γ (colorizeAssocData d) =
      Operad.associativityRouteB (uncolorCollection O) (uncolorSubst O γ) d := by
  let groupAHom := uncolorGroupingAHom O d
  let groupBHom := uncolorGroupingBHom O d
  let flatAHom := (FiniteFamily.flatten (C := V)).map groupAHom
  let flatBHom := (FiniteFamily.flatten (C := V)).map groupBHom
  let flattenCol :
      (FiniteFamily.flatten (C := V)).obj
          (ColoredOperadObj.AssocInsertion.groupingA O (colorizeAssocData d)) ⟶
        (FiniteFamily.flatten (C := V)).obj
          (ColoredOperadObj.AssocInsertion.groupingB O (colorizeAssocData d)) := by
    with_unfolding_all
      exact ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O (colorizeAssocData d)
  let flattenOrd :
      (FiniteFamily.flatten (C := V)).obj
          (Operad.AssocInsertion.groupingA (uncolorCollection O) d) ⟶
        (FiniteFamily.flatten (C := V)).obj
          (Operad.AssocInsertion.groupingB (uncolorCollection O) d) := by
    with_unfolding_all
      exact Operad.AssocInsertion.flattenAToFlattenBHom (uncolorCollection O) d
  let mappedGroupBHom :=
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map groupBHom
  let groupCol :=
    ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O γ (colorizeAssocData d)
  let groupOrd :=
    Operad.AssocInsertion.groupingBToFactorsHom
      (uncolorCollection O) (uncolorSubst O γ) d
  let factor :
      (Operad.substitutionFactors (uncolorCollection O)).obj d.innerData ⟶
        (ColoredOperadObj.substitutionFactors O).obj (colorizeAssocData d).innerData := by
    with_unfolding_all exact uncolorFactorHom O d.innerData
  let innerCol :
      (FiniteTensor.tensor (V := V)).obj
          ((ColoredOperadObj.substitutionFactors O).obj (colorizeAssocData d).innerData) ⟶
        O.obj (colorizeAssocData d).innerData.totalProfile :=
    γ.app (colorizeAssocData d).innerData
  let innerOrd :
      (FiniteTensor.tensor (V := V)).obj
          ((Operad.substitutionFactors (uncolorCollection O)).obj d.innerData) ⟶
        O.obj (colorizeAssocData d).innerData.totalProfile := by
    with_unfolding_all exact (uncolorSubst O γ).app d.innerData
  let relabelCol :
      O.obj (colorizeAssocData d).innerData.totalProfile ⟶
        O.obj (colorizeAssocData d).outerAfterInnerData.totalProfile :=
    O.map (colorizeAssocData d).totalHom
  let relabelOrd :
      O.obj (colorizeAssocData d).innerData.totalProfile ⟶
        O.obj (colorizeAssocData d).outerAfterInnerData.totalProfile := by
    with_unfolding_all exact (uncolorCollection O).relabelIso d.totalIso
  have hFlat : flatAHom ≫ flattenCol = flattenOrd ≫ flatBHom := by
    with_unfolding_all exact uncolorFlattenAToFlattenB_compat O d
  have hFlatTensor :
      (FiniteTensor.tensor (V := V)).map flatAHom ≫
          (FiniteTensor.tensor (V := V)).map flattenCol =
        (FiniteTensor.tensor (V := V)).map flattenOrd ≫
          (FiniteTensor.tensor (V := V)).map flatBHom := by
    calc
      _ = (FiniteTensor.tensor (V := V)).map (flatAHom ≫ flattenCol) :=
        ((FiniteTensor.tensor (V := V)).map_comp flatAHom flattenCol).symm
      _ = (FiniteTensor.tensor (V := V)).map (flattenOrd ≫ flatBHom) :=
        congrArg (fun f => (FiniteTensor.tensor (V := V)).map f) hFlat
      _ = _ := (FiniteTensor.tensor (V := V)).map_comp flattenOrd flatBHom
  have hFlattenB :
      (FiniteTensor.tensor (V := V)).map flatBHom ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (ColoredOperadObj.AssocInsertion.groupingB O (colorizeAssocData d)) =
      (FiniteTensor.flattenIso (V := V)).hom.app
        (Operad.AssocInsertion.groupingB (uncolorCollection O) d) ≫
        (FiniteTensor.tensor (V := V)).map mappedGroupBHom := by
    with_unfolding_all
      exact (FiniteTensor.flattenIso (V := V)).hom.naturality groupBHom
  have hGroup : mappedGroupBHom ≫ groupCol = groupOrd ≫ factor := by
    with_unfolding_all exact uncolorGroupingBToFactors_compat O γ d
  have hGroupTensor :
      (FiniteTensor.tensor (V := V)).map mappedGroupBHom ≫
          (FiniteTensor.tensor (V := V)).map groupCol =
        (FiniteTensor.tensor (V := V)).map groupOrd ≫
          (FiniteTensor.tensor (V := V)).map factor := by
    calc
      _ = (FiniteTensor.tensor (V := V)).map (mappedGroupBHom ≫ groupCol) :=
        ((FiniteTensor.tensor (V := V)).map_comp mappedGroupBHom groupCol).symm
      _ = (FiniteTensor.tensor (V := V)).map (groupOrd ≫ factor) :=
        congrArg (fun f => (FiniteTensor.tensor (V := V)).map f) hGroup
      _ = _ := (FiniteTensor.tensor (V := V)).map_comp groupOrd factor
  have hInner :
      (FiniteTensor.tensor (V := V)).map factor ≫ innerCol = innerOrd := by
    rfl
  have hRelabel : relabelCol = relabelOrd := by
    rfl
  change (FiniteTensor.tensor (V := V)).map flatAHom ≫
      ((FiniteTensor.tensor (V := V)).map flattenCol ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          (ColoredOperadObj.AssocInsertion.groupingB O (colorizeAssocData d)) ≫
        (FiniteTensor.tensor (V := V)).map groupCol ≫ innerCol ≫ relabelCol) =
    (FiniteTensor.tensor (V := V)).map flattenOrd ≫
      (FiniteTensor.flattenIso (V := V)).hom.app
        (Operad.AssocInsertion.groupingB (uncolorCollection O) d) ≫
      (FiniteTensor.tensor (V := V)).map groupOrd ≫ innerOrd ≫ relabelOrd
  slice_lhs 1 2 => rw [hFlatTensor]
  slice_lhs 2 3 => rw [hFlattenB]
  slice_lhs 3 4 => rw [hGroupTensor]
  slice_lhs 4 5 => rw [hInner]
  rw [hRelabel]

end CategoryTheory.Operad.ColoredOperadObj.OneColor

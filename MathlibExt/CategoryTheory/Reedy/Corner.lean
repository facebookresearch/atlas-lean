/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.Boundary
public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# Actual relative corner functors, comparisons and retracts

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  {F G : J ⥤ C} (f : F ⟶ G) (j : J)

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The original chosen latching colimit is canonically isomorphic to the full canonical one. -/
def latchingColimitIso (X : J ⥤ C) (c : Cocone (r.latchingDiagram X j)) (hc : IsColimit c) :
    c.pt ≅ colimit (r.latchingDiagram X j) :=
  hc.coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc]
theorem latchingColimitIso_ι (X : J ⥤ C) (c : Cocone (r.latchingDiagram X j))
    (hc : IsColimit c) (a : r.Latching j) :
    c.ι.app a ≫ (latchingColimitIso r j X c hc).hom = colimit.ι (r.latchingDiagram X j) a :=
  IsColimit.comp_coconePointUniqueUpToIso_hom hc (colimit.isColimit _) a

@[reassoc]
theorem latchingColimitIso_inv_ι (X : J ⥤ C) (c : Cocone (r.latchingDiagram X j))
    (hc : IsColimit c) (a : r.Latching j) :
    colimit.ι (r.latchingDiagram X j) a ≫ (latchingColimitIso r j X c hc).inv = c.ι.app a :=
  IsColimit.comp_coconePointUniqueUpToIso_inv hc (colimit.isColimit _) a

/-- The chosen-to-canonical latching isomorphism retains the entire original latching map. -/
theorem latchingMapWith_colimitIso (X : J ⥤ C) (c : Cocone (r.latchingDiagram X j))
    (hc : IsColimit c) : r.latchingMapWith X j c hc =
      (latchingColimitIso r j X c hc).hom ≫ latchingMap r X j := by
  apply hc.hom_ext
  intro a
  rw [r.latchingMapWith_ι, ← Category.assoc, latchingColimitIso_ι r, latchingMap_ι r]

/-- The complete original transformation commutes with every chosen-to-canonical latching
comparison. -/
theorem latchingComparisonWith_colimitIso
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY) :
    r.latchingComparisonWith f j cX hX cY ≫ (latchingColimitIso r j G cY hY).hom =
      (latchingColimitIso r j F cX hX).hom ≫ colimMap (r.latchingTransformation f j) := by
  apply hX.hom_ext
  intro a
  rw [← Category.assoc, r.latchingComparisonWith_ι, Category.assoc,
    latchingColimitIso_ι r, ← Category.assoc, latchingColimitIso_ι r, ι_colimMap]
  rfl

variable [HasPushouts C]

/-- Compare the complete chosen and canonical latching corner source pushouts. -/
def latchingPushoutComparison
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY) :
    pushout (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY) ≅
      pushout (latchingMap r F j) (colimMap (r.latchingTransformation f j)) :=
  asIso (pushout.map _ _ _ _ (𝟙 (F.obj j))
    (latchingColimitIso r j G cY hY).hom (latchingColimitIso r j F cX hX).hom
    (by rw [Category.comp_id]; exact latchingMapWith_colimitIso r j F cX hX)
    (latchingComparisonWith_colimitIso r f j cX hX cY hY))

@[reassoc]
theorem latchingPushoutComparison_inl
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY) :
    pushout.inl (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY) ≫
      (latchingPushoutComparison r f j cX hX cY hY).hom =
      pushout.inl (latchingMap r F j) (colimMap (r.latchingTransformation f j)) := by
  simp only [latchingPushoutComparison, asIso_hom, pushout.map, pushout.inl_desc, Category.id_comp]

@[reassoc]
theorem latchingPushoutComparison_inr
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY) :
    pushout.inr (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY) ≫
      (latchingPushoutComparison r f j cX hX cY hY).hom =
      (latchingColimitIso r j G cY hY).hom ≫
        pushout.inr (latchingMap r F j) (colimMap (r.latchingTransformation f j)) := by
  simp only [latchingPushoutComparison, asIso_hom, pushout.map, pushout.inr_desc]

/-- Every original caller complete latching pushout is compared to the canonical corner source. -/
def latchingCornerSourceIso
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) : cP.pt ≅
      pushout (latchingMap r F j) (colimMap (r.latchingTransformation f j)) :=
  (colimit.isoColimitCocone ⟨cP, hP⟩).symm ≪≫ latchingPushoutComparison r f j cX hX cY hY

@[reassoc]
theorem latchingCornerSourceIso_inl
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) : cP.inl ≫ (latchingCornerSourceIso r f j cX hX cY hY cP hP).hom =
      pushout.inl (latchingMap r F j) (colimMap (r.latchingTransformation f j)) := by
  have hp : cP.inl ≫ (colimit.isoColimitCocone ⟨cP, hP⟩).inv =
      pushout.inl (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY) :=
    colimit.isoColimitCocone_ι_inv ⟨cP, hP⟩ WalkingSpan.left
  rw [latchingCornerSourceIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hp,
    latchingPushoutComparison_inl r]

@[reassoc]
theorem latchingCornerSourceIso_inr
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) : cP.inr ≫ (latchingCornerSourceIso r f j cX hX cY hY cP hP).hom =
      (latchingColimitIso r j G cY hY).hom ≫
        pushout.inr (latchingMap r F j) (colimMap (r.latchingTransformation f j)) := by
  have hp : cP.inr ≫ (colimit.isoColimitCocone ⟨cP, hP⟩).inv =
      pushout.inr (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY) :=
    colimit.isoColimitCocone_ι_inv ⟨cP, hP⟩ WalkingSpan.right
  rw [latchingCornerSourceIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hp,
    latchingPushoutComparison_inr r]

/-- The complete original chosen corner map is the canonical map under its full source
comparison. -/
theorem latchingCornerWith_comparison
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) :
    (latchingCornerSourceIso r f j cX hX cY hY cP hP).hom ≫ latchingCorner r f j =
      r.latchingCornerWith f j cX hX cY hY cP hP := by
  apply PushoutCocone.IsColimit.hom_ext hP
  · rw [← Category.assoc, latchingCornerSourceIso_inl r,
      latchingCorner_inl r, r.latchingCornerWith_inl]
  · rw [← Category.assoc, latchingCornerSourceIso_inr r, Category.assoc,
      latchingCorner_inr r, r.latchingCornerWith_inr]
    exact (latchingMapWith_colimitIso r j G cY hY).symm

/-- The full original caller latching corner and canonical corner are isomorphic as arrows. -/
def latchingCornerWithArrowIso
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) :
    Arrow.mk (r.latchingCornerWith f j cX hX cY hY cP hP) ≅ Arrow.mk (latchingCorner r f j) :=
  Arrow.isoMk' _ _ (latchingCornerSourceIso r f j cX hX cY hY cP hP) (Iso.refl (G.obj j))
    (by rw [Iso.refl_hom, Category.comp_id];
        exact latchingCornerWith_comparison r f j cX hX cY hY cP hP)

/-- Every source class respecting isomorphisms recognizes the same original caller latching
corner. -/
theorem latchingCornerWith_mem_iff (P : MorphismProperty C) [P.RespectsIso]
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) :
    P (r.latchingCornerWith f j cX hX cY hY cP hP) ↔ P (latchingCorner r f j) :=
  P.arrow_mk_iso_iff (latchingCornerWithArrowIso r f j cX hX cY hY cP hP)

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The original chosen matching limit is canonically isomorphic to the full canonical one. -/
def matchingLimitIso (X : J ⥤ C) (c : Cone (r.matchingDiagram X j)) (hc : IsLimit c) :
    c.pt ≅ limit (r.matchingDiagram X j) :=
  hc.conePointUniqueUpToIso (limit.isLimit _)

@[reassoc]
theorem matchingLimitIso_π (X : J ⥤ C) (c : Cone (r.matchingDiagram X j))
    (hc : IsLimit c) (a : r.Matching j) :
    (matchingLimitIso r j X c hc).hom ≫ limit.π (r.matchingDiagram X j) a = c.π.app a :=
  IsLimit.conePointUniqueUpToIso_hom_comp hc (limit.isLimit _) a

@[reassoc]
theorem matchingLimitIso_inv_π (X : J ⥤ C) (c : Cone (r.matchingDiagram X j))
    (hc : IsLimit c) (a : r.Matching j) :
    (matchingLimitIso r j X c hc).inv ≫ c.π.app a = limit.π (r.matchingDiagram X j) a :=
  IsLimit.conePointUniqueUpToIso_inv_comp hc (limit.isLimit _) a

/-- The chosen-to-canonical matching isomorphism retains the entire original matching map. -/
theorem matchingMapWith_limitIso (X : J ⥤ C) (c : Cone (r.matchingDiagram X j))
    (hc : IsLimit c) : r.matchingMapWith X j c hc ≫ (matchingLimitIso r j X c hc).hom =
      matchingMap r X j := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, matchingLimitIso_π r, r.matchingMapWith_π, matchingMap_π r]

/-- The complete original transformation commutes with every chosen-to-canonical matching
comparison. -/
theorem matchingComparisonWith_limitIso
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY) :
    r.matchingComparisonWith f j cX cY hY ≫ (matchingLimitIso r j G cY hY).hom =
      (matchingLimitIso r j F cX hX).hom ≫ limMap (r.matchingTransformation f j) := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, matchingLimitIso_π r, r.matchingComparisonWith_π,
    Category.assoc, limMap_π, ← Category.assoc, matchingLimitIso_π r]
  rfl

variable [HasPullbacks C]

/-- Compare the complete chosen and canonical matching corner target pullbacks. -/
def matchingPullbackComparison
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY) :
    pullback (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY) ≅
      pullback (limMap (r.matchingTransformation f j)) (matchingMap r G j) :=
  asIso (pullback.map _ _ _ _ (matchingLimitIso r j F cX hX).hom (𝟙 (G.obj j))
    (matchingLimitIso r j G cY hY).hom
    (matchingComparisonWith_limitIso r f j cX hX cY hY)
    (by rw [Category.id_comp]; exact matchingMapWith_limitIso r j G cY hY))

@[reassoc]
theorem matchingPullbackComparison_fst
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY) :
    (matchingPullbackComparison r f j cX hX cY hY).hom ≫
      pullback.fst (limMap (r.matchingTransformation f j)) (matchingMap r G j) =
      pullback.fst (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY) ≫
        (matchingLimitIso r j F cX hX).hom := by
  simp only [matchingPullbackComparison, asIso_hom, pullback.map, pullback.lift_fst]

@[reassoc]
theorem matchingPullbackComparison_snd
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY) :
    (matchingPullbackComparison r f j cX hX cY hY).hom ≫
      pullback.snd (limMap (r.matchingTransformation f j)) (matchingMap r G j) =
      pullback.snd (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY) := by
  simp only [matchingPullbackComparison, asIso_hom, pullback.map, pullback.lift_snd,
    Category.comp_id]

/-- Every original caller complete matching pullback is compared to the canonical corner target. -/
def matchingCornerTargetIso
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY))
    (hP : IsLimit cP) : cP.pt ≅
      pullback (limMap (r.matchingTransformation f j)) (matchingMap r G j) :=
  (limit.isoLimitCone ⟨cP, hP⟩).symm ≪≫ matchingPullbackComparison r f j cX hX cY hY

@[reassoc]
theorem matchingCornerTargetIso_fst
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY))
    (hP : IsLimit cP) : (matchingCornerTargetIso r f j cX hX cY hY cP hP).hom ≫
      pullback.fst (limMap (r.matchingTransformation f j)) (matchingMap r G j) =
      cP.fst ≫ (matchingLimitIso r j F cX hX).hom := by
  have hp : (limit.isoLimitCone ⟨cP, hP⟩).inv ≫
      pullback.fst (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY) = cP.fst :=
    limit.isoLimitCone_inv_π ⟨cP, hP⟩ WalkingCospan.left
  rw [matchingCornerTargetIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    matchingPullbackComparison_fst r, ← Category.assoc, hp]

@[reassoc]
theorem matchingCornerTargetIso_snd
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY))
    (hP : IsLimit cP) : (matchingCornerTargetIso r f j cX hX cY hY cP hP).hom ≫
      pullback.snd (limMap (r.matchingTransformation f j)) (matchingMap r G j) = cP.snd := by
  have hp : (limit.isoLimitCone ⟨cP, hP⟩).inv ≫
      pullback.snd (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY) = cP.snd :=
    limit.isoLimitCone_inv_π ⟨cP, hP⟩ WalkingCospan.right
  rw [matchingCornerTargetIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    matchingPullbackComparison_snd r, hp]

/-- The complete original chosen corner map is the canonical map under its full target
comparison. -/
theorem matchingCornerWith_comparison
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY))
    (hP : IsLimit cP) :
    r.matchingCornerWith f j cX hX cY hY cP hP ≫
      (matchingCornerTargetIso r f j cX hX cY hY cP hP).hom = matchingCorner r f j := by
  apply pullback.hom_ext
  · rw [Category.assoc, matchingCornerTargetIso_fst r, ← Category.assoc,
      r.matchingCornerWith_fst, matchingMapWith_limitIso r, matchingCorner_fst r]
  · rw [Category.assoc, matchingCornerTargetIso_snd r,
      r.matchingCornerWith_snd, matchingCorner_snd r]

/-- The full original caller matching corner and canonical corner are isomorphic as arrows. -/
def matchingCornerWithArrowIso
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY))
    (hP : IsLimit cP) :
    Arrow.mk (r.matchingCornerWith f j cX hX cY hY cP hP) ≅ Arrow.mk (matchingCorner r f j) :=
  Arrow.isoMk' _ _ (Iso.refl (F.obj j)) (matchingCornerTargetIso r f j cX hX cY hY cP hP)
    (by rw [Iso.refl_hom, Category.id_comp];
        exact (matchingCornerWith_comparison r f j cX hX cY hY cP hP).symm)

/-- Every source class respecting isomorphisms recognizes the same original caller matching
corner. -/
theorem matchingCornerWith_mem_iff (P : MorphismProperty C) [P.RespectsIso]
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY))
    (hP : IsLimit cP) :
    P (r.matchingCornerWith f j cX hX cY hY cP hP) ↔ P (matchingCorner r f j) :=
  P.arrow_mk_iso_iff (matchingCornerWithArrowIso r f j cX hX cY hY cP hP)

end Matching

end CategoryTheory.ReedyStructure

end ReedyPart1

section ReedyPart2

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The full original latching comparison retains the original diagram identity. -/
theorem latchingColimMap_id (F : J ⥤ C) (j : J) :
    colimMap (r.latchingTransformation (𝟙 F) j) = 𝟙 (colimit (r.latchingDiagram F j)) := by
  apply colimit.hom_ext
  intro a
  rw [ι_colimMap]
  change (𝟙 (F.obj (r.latchingSource a))) ≫ colimit.ι (r.latchingDiagram F j) a =
    colimit.ι (r.latchingDiagram F j) a ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

/-- The full original latching comparisons retain the original diagram composition. -/
theorem latchingColimMap_comp {F G H : J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) (j : J) :
    colimMap (r.latchingTransformation (f ≫ g) j) =
      colimMap (r.latchingTransformation f j) ≫ colimMap (r.latchingTransformation g j) := by
  simpa only [latchingTransformation, Functor.whiskerLeft_comp, colimMap_eq] using
    (colim.map_comp (r.latchingTransformation f j) (r.latchingTransformation g j))

/-- Every original natural square commutes on its full latching colimit comparisons. -/
theorem latchingColimMap_square {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    colimMap (r.latchingTransformation f.hom j) ≫ colimMap (r.latchingTransformation s.right j) =
      colimMap (r.latchingTransformation s.left j) ≫
        colimMap (r.latchingTransformation g.hom j) := by
  rw [← latchingColimMap_comp r, ← latchingColimMap_comp r, ← s.w]

variable [HasPushouts C]

/-- The exact original pushout comparison induced by a full original natural square. -/
def latchingCornerSourceMap {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    pushout (latchingMap r f.left j) (colimMap (r.latchingTransformation f.hom j)) ⟶
      pushout (latchingMap r g.left j) (colimMap (r.latchingTransformation g.hom j)) :=
  pushout.map _ _ _ _ (s.left.app j) (colimMap (r.latchingTransformation s.right j))
    (colimMap (r.latchingTransformation s.left j))
    (latchingMap_naturality r s.left j) (latchingColimMap_square r s j)

@[reassoc]
theorem latchingCornerSourceMap_inl {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    pushout.inl (latchingMap r f.left j) (colimMap (r.latchingTransformation f.hom j)) ≫
      latchingCornerSourceMap r s j = s.left.app j ≫
        pushout.inl (latchingMap r g.left j) (colimMap (r.latchingTransformation g.hom j)) :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem latchingCornerSourceMap_inr {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    pushout.inr (latchingMap r f.left j) (colimMap (r.latchingTransformation f.hom j)) ≫
      latchingCornerSourceMap r s j = colimMap (r.latchingTransformation s.right j) ≫
        pushout.inr (latchingMap r g.left j) (colimMap (r.latchingTransformation g.hom j)) :=
  pushout.inr_desc _ _ _

/-- The exact original pushout comparisons preserve the original square identity. -/
theorem latchingCornerSourceMap_id (f : Arrow (J ⥤ C)) (j : J) :
    latchingCornerSourceMap r (𝟙 f) j =
      𝟙 (pushout (latchingMap r f.left j) (colimMap (r.latchingTransformation f.hom j))) := by
  apply pushout.hom_ext
  · rw [latchingCornerSourceMap_inl r, Arrow.id_left, NatTrans.id_app,
      Category.id_comp, Category.comp_id]
  · rw [latchingCornerSourceMap_inr r, Arrow.id_right, latchingColimMap_id r,
      Category.id_comp, Category.comp_id]

/-- The exact original pushout comparisons preserve all original square compositions. -/
theorem latchingCornerSourceMap_comp {f g h : Arrow (J ⥤ C)} (s : f ⟶ g) (t : g ⟶ h) (j : J) :
    latchingCornerSourceMap r (s ≫ t) j =
      latchingCornerSourceMap r s j ≫ latchingCornerSourceMap r t
      j := by
  apply pushout.hom_ext
  · rw [latchingCornerSourceMap_inl r, ← Category.assoc, latchingCornerSourceMap_inl r,
      Category.assoc, latchingCornerSourceMap_inl r, Arrow.comp_left,
        NatTrans.comp_app, Category.assoc]
  · rw [latchingCornerSourceMap_inr r, ← Category.assoc, latchingCornerSourceMap_inr r,
      Category.assoc, latchingCornerSourceMap_inr r, Arrow.comp_right, latchingColimMap_comp r,
        Category.assoc]

/-- The same original natural square commutes on its unchanged latching corner maps. -/
theorem latchingCornerSourceMap_corner {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    latchingCornerSourceMap r s j ≫ latchingCorner r g.hom j =
      latchingCorner r f.hom j ≫ s.right.app j := by
  apply pushout.hom_ext
  · rw [← Category.assoc, latchingCornerSourceMap_inl r, Category.assoc,
      latchingCorner_inl r, ← Category.assoc, latchingCorner_inl r]
    exact congr_app s.w j
  · rw [← Category.assoc, latchingCornerSourceMap_inr r, Category.assoc,
      latchingCorner_inr r, ← Category.assoc, latchingCorner_inr r]
    exact (latchingMap_naturality r s.right j).symm

/-- The actual latching corner is an Arrow functor on all original diagram arrows and squares. -/
def latchingCornerArrow (j : J) : Arrow (J ⥤ C) ⥤ Arrow C where
  obj f := Arrow.mk (latchingCorner r f.hom j)
  map s := Arrow.homMk (latchingCornerSourceMap r s j) (s.right.app j)
    (latchingCornerSourceMap_corner r s j)
  map_id f := by
    apply Arrow.hom_ext
    · exact latchingCornerSourceMap_id r f j
    · rfl
  map_comp s t := by
    apply Arrow.hom_ext
    · exact latchingCornerSourceMap_comp r s t j
    · rfl

@[simp]
theorem latchingCornerArrow_obj_hom (j : J) (f : Arrow (J ⥤ C)) :
    ((latchingCornerArrow r j).obj f).hom = latchingCorner r f.hom j := rfl

@[simp]
theorem latchingCornerArrow_map_left (j : J) {f g : Arrow (J ⥤ C)} (s : f ⟶ g) :
    ((latchingCornerArrow r j).map s).left = latchingCornerSourceMap r s j := rfl

@[simp]
theorem latchingCornerArrow_map_right (j : J) {f g : Arrow (J ⥤ C)} (s : f ⟶ g) :
    ((latchingCornerArrow r j).map s).right = s.right.app j := rfl

/-- The same original diagram retract induces a retract of the same actual latching corners. -/
def latchingCornerRetract {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) : RetractArrow (latchingCorner r f j) (latchingCorner r g j) :=
  Retract.map h (latchingCornerArrow r j)

/-- The original latching source splitting equations are retained by the actual pushout
comparisons. -/
theorem latchingCornerRetract_source {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    latchingCornerSourceMap r h.i j ≫ latchingCornerSourceMap r h.r j =
      𝟙 (pushout (latchingMap r F j) (colimMap (r.latchingTransformation f j))) :=
  (latchingCornerRetract r h j).retract_left

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C] in
/-- The original latching target splitting equations remain the original component equations. -/
theorem latchingCornerRetract_target {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) : h.i.right.app j ≫ h.r.right.app j = 𝟙 (G.obj j) :=
  congr_app h.retract_right j

@[simp]
theorem latchingCornerRetract_i_left {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    (latchingCornerRetract r h j).i.left = latchingCornerSourceMap r h.i j := rfl

@[simp]
theorem latchingCornerRetract_i_right {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) : (latchingCornerRetract r h j).i.right = h.i.right.app j := rfl

@[simp]
theorem latchingCornerRetract_r_left {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    (latchingCornerRetract r h j).r.left = latchingCornerSourceMap r h.r j := rfl

@[simp]
theorem latchingCornerRetract_r_right {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) : (latchingCornerRetract r h j).r.right = h.r.right.app j := rfl

/-- The unchanged original retract inclusion square commutes on the actual latching corners. -/
theorem latchingCornerRetract_i_w {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    latchingCornerSourceMap r h.i j ≫ latchingCorner r g j =
      latchingCorner r f j ≫ h.i.right.app j :=
  (latchingCornerRetract r h j).i_w

/-- The unchanged original retract retraction square commutes on the actual latching corners. -/
theorem latchingCornerRetract_r_w {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    latchingCornerSourceMap r h.r j ≫ latchingCorner r f j =
      latchingCorner r g j ≫ h.r.right.app j :=
  (latchingCornerRetract r h j).r_w

/-- The full actual latching-corner Arrow splitting equation is retained. -/
theorem latchingCornerRetract_equation {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    (latchingCornerArrow r j).map h.i ≫ (latchingCornerArrow r j).map h.r =
      𝟙 ((latchingCornerArrow r j).obj (Arrow.mk f)) := (latchingCornerRetract r h j).retract

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The full original matching comparison retains the original diagram identity. -/
theorem matchingLimMap_id (F : J ⥤ C) (j : J) :
    limMap (r.matchingTransformation (𝟙 F) j) = 𝟙 (limit (r.matchingDiagram F j)) := by
  apply limit.hom_ext
  intro a
  rw [limMap_π]
  let π : limit (r.matchingDiagram F j) ⟶ F.obj (r.matchingTarget a) :=
    limit.π (r.matchingDiagram F j) a
  change π ≫ (𝟙 (F.obj (r.matchingTarget a))) = 𝟙 _ ≫ π
  rw [Category.comp_id, Category.id_comp]

/-- The full original matching comparisons retain the original diagram composition. -/
theorem matchingLimMap_comp {F G H : J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) (j : J) :
    limMap (r.matchingTransformation (f ≫ g) j) =
      limMap (r.matchingTransformation f j) ≫ limMap (r.matchingTransformation g j) := by
  simpa only [matchingTransformation, Functor.whiskerLeft_comp, limMap_eq] using
    (lim.map_comp (r.matchingTransformation f j) (r.matchingTransformation g j))

/-- Every original natural square commutes on its full matching limit comparisons. -/
theorem matchingLimMap_square {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    limMap (r.matchingTransformation f.hom j) ≫ limMap (r.matchingTransformation s.right j) =
      limMap (r.matchingTransformation s.left j) ≫ limMap (r.matchingTransformation g.hom j) := by
  rw [← matchingLimMap_comp r, ← matchingLimMap_comp r, ← s.w]

variable [HasPullbacks C]

/-- The exact original pullback comparison induced by a full original natural square. -/
def matchingCornerTargetMap {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    pullback (limMap (r.matchingTransformation f.hom j)) (matchingMap r f.right j) ⟶
      pullback (limMap (r.matchingTransformation g.hom j)) (matchingMap r g.right j) :=
  pullback.map _ _ _ _ (limMap (r.matchingTransformation s.left j)) (s.right.app j)
    (limMap (r.matchingTransformation s.right j))
    (matchingLimMap_square r s j) (matchingMap_naturality r s.right j)

@[reassoc]
theorem matchingCornerTargetMap_fst {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    matchingCornerTargetMap r s j ≫
      pullback.fst (limMap (r.matchingTransformation g.hom j)) (matchingMap r g.right j) =
      pullback.fst (limMap (r.matchingTransformation f.hom j)) (matchingMap r f.right j) ≫
        limMap (r.matchingTransformation s.left j) := pullback.lift_fst _ _ _

@[reassoc]
theorem matchingCornerTargetMap_snd {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    matchingCornerTargetMap r s j ≫
      pullback.snd (limMap (r.matchingTransformation g.hom j)) (matchingMap r g.right j) =
      pullback.snd (limMap (r.matchingTransformation f.hom j)) (matchingMap r f.right j) ≫
        s.right.app j := pullback.lift_snd _ _ _

/-- The exact original pullback comparisons preserve the original square identity. -/
theorem matchingCornerTargetMap_id (f : Arrow (J ⥤ C)) (j : J) :
    matchingCornerTargetMap r (𝟙 f) j =
      𝟙 (pullback (limMap (r.matchingTransformation f.hom j)) (matchingMap r f.right j)) := by
  apply pullback.hom_ext
  · rw [matchingCornerTargetMap_fst r, Arrow.id_left, matchingLimMap_id r,
      Category.comp_id, Category.id_comp]
  · rw [matchingCornerTargetMap_snd r, Arrow.id_right, NatTrans.id_app,
      Category.comp_id, Category.id_comp]

/-- The exact original pullback comparisons preserve all original square compositions. -/
theorem matchingCornerTargetMap_comp {f g h : Arrow (J ⥤ C)} (s : f ⟶ g) (t : g ⟶ h) (j : J) :
    matchingCornerTargetMap r (s ≫ t) j =
      matchingCornerTargetMap r s j ≫ matchingCornerTargetMap r t
      j := by
  apply pullback.hom_ext
  · rw [matchingCornerTargetMap_fst r, Category.assoc, matchingCornerTargetMap_fst r,
      ← Category.assoc, matchingCornerTargetMap_fst r, Arrow.comp_left, matchingLimMap_comp r,
        Category.assoc]
  · rw [matchingCornerTargetMap_snd r, Category.assoc, matchingCornerTargetMap_snd r,
      ← Category.assoc, matchingCornerTargetMap_snd r, Arrow.comp_right,
        NatTrans.comp_app, Category.assoc]

/-- The same original natural square commutes on its unchanged matching corner maps. -/
theorem matchingCornerTargetMap_corner {f g : Arrow (J ⥤ C)} (s : f ⟶ g) (j : J) :
    s.left.app j ≫ matchingCorner r g.hom j =
      matchingCorner r f.hom j ≫ matchingCornerTargetMap r s j
      := by
  apply pullback.hom_ext
  · rw [Category.assoc, matchingCorner_fst r, Category.assoc,
      matchingCornerTargetMap_fst r, ← Category.assoc, matchingCorner_fst r]
    exact (matchingMap_naturality r s.left j).symm
  · rw [Category.assoc, matchingCorner_snd r, Category.assoc,
      matchingCornerTargetMap_snd r, ← Category.assoc, matchingCorner_snd r]
    exact congr_app s.w j

/-- The actual matching corner is an Arrow functor on all original diagram arrows and squares. -/
def matchingCornerArrow (j : J) : Arrow (J ⥤ C) ⥤ Arrow C where
  obj f := Arrow.mk (matchingCorner r f.hom j)
  map s := Arrow.homMk (s.left.app j) (matchingCornerTargetMap r s j)
    (matchingCornerTargetMap_corner r s j)
  map_id f := by
    apply Arrow.hom_ext
    · rfl
    · exact matchingCornerTargetMap_id r f j
  map_comp s t := by
    apply Arrow.hom_ext
    · rfl
    · exact matchingCornerTargetMap_comp r s t j

@[simp]
theorem matchingCornerArrow_obj_hom (j : J) (f : Arrow (J ⥤ C)) :
    ((matchingCornerArrow r j).obj f).hom = matchingCorner r f.hom j := rfl

@[simp]
theorem matchingCornerArrow_map_left (j : J) {f g : Arrow (J ⥤ C)} (s : f ⟶ g) :
    ((matchingCornerArrow r j).map s).left = s.left.app j := rfl

@[simp]
theorem matchingCornerArrow_map_right (j : J) {f g : Arrow (J ⥤ C)} (s : f ⟶ g) :
    ((matchingCornerArrow r j).map s).right = matchingCornerTargetMap r s j := rfl

/-- The same original diagram retract induces a retract of the same actual matching corners. -/
def matchingCornerRetract {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) : RetractArrow (matchingCorner r f j) (matchingCorner r g j) :=
  Retract.map h (matchingCornerArrow r j)

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C] in
/-- The original matching source splitting equations remain the original component equations. -/
theorem matchingCornerRetract_source {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) : h.i.left.app j ≫ h.r.left.app j = 𝟙 (F.obj j) :=
  congr_app h.retract_left j

/-- The original matching target splitting equations are retained by the actual pullback
comparisons. -/
theorem matchingCornerRetract_target {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) : matchingCornerTargetMap r h.i j ≫
      matchingCornerTargetMap r h.r j =
      𝟙 (pullback (limMap (r.matchingTransformation f j)) (matchingMap r G j)) :=
  (matchingCornerRetract r h j).retract_right

@[simp]
theorem matchingCornerRetract_i_left {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) : (matchingCornerRetract r h j).i.left = h.i.left.app j := rfl

@[simp]
theorem matchingCornerRetract_i_right {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    (matchingCornerRetract r h j).i.right = matchingCornerTargetMap r h.i j := rfl

@[simp]
theorem matchingCornerRetract_r_left {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) : (matchingCornerRetract r h j).r.left = h.r.left.app j := rfl

@[simp]
theorem matchingCornerRetract_r_right {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    (matchingCornerRetract r h j).r.right = matchingCornerTargetMap r h.r j := rfl

/-- The unchanged original retract inclusion square commutes on the actual matching corners. -/
theorem matchingCornerRetract_i_w {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    h.i.left.app j ≫ matchingCorner r g j =
      matchingCorner r f j ≫ matchingCornerTargetMap r h.i j :=
  (matchingCornerRetract r h j).i_w

/-- The unchanged original retract retraction square commutes on the actual matching corners. -/
theorem matchingCornerRetract_r_w {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    h.r.left.app j ≫ matchingCorner r f j =
      matchingCorner r g j ≫ matchingCornerTargetMap r h.r j :=
  (matchingCornerRetract r h j).r_w

/-- The full actual matching-corner Arrow splitting equation is retained. -/
theorem matchingCornerRetract_equation {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}
    (h : RetractArrow f g) (j : J) :
    (matchingCornerArrow r j).map h.i ≫ (matchingCornerArrow r j).map h.r =
      𝟙 ((matchingCornerArrow r j).obj (Arrow.mk f)) := (matchingCornerRetract r h j).retract

end Matching

end CategoryTheory.ReedyStructure

end ReedyPart2

section ReedyPart3

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- Membership in the original relative latching class at every original source object. -/
def latchingClass [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]
    (P : MorphismProperty C) : MorphismProperty (J ⥤ C) :=
  fun {_ _} f ↦ ∀ j, P (latchingCorner r f j)

/-- Membership in the original relative matching class at every original source object. -/
def matchingClass [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]
    (Q : MorphismProperty C) : MorphismProperty (J ⥤ C) :=
  fun {_ _} f ↦ ∀ j, Q (matchingCorner r f j)

end CategoryTheory.ReedyStructure

end ReedyPart3

section ReedyPart6

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- The actual shape latching corner functor retains source retract stability. -/
instance latchingClass_isStableUnderRetracts
    [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]
    (P : MorphismProperty C) [P.IsStableUnderRetracts] :
      (latchingClass r P).IsStableUnderRetracts where
  of_retract h hg j := MorphismProperty.of_retract (latchingCornerRetract r h j) (hg j)

/-- The actual shape matching corner functor retains source retract stability. -/
instance matchingClass_isStableUnderRetracts
    [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderRetracts] :
      (matchingClass r P).IsStableUnderRetracts where
  of_retract h hg j := MorphismProperty.of_retract (matchingCornerRetract r h j) (hg j)

end CategoryTheory.ReedyStructure

end ReedyPart6

section ReedyPart7

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure.PostcomposeCorners

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
  (T : C ⥤ B) {X Y : J ⥤ C} (f : X ⟶ Y) (j : J)

/-- Equal original span maps preserve the complete universal property of the same given
injections. -/
def pushoutMkIsColimitOfEq {A₀ A₁ A₂ A₃ : B} {u u' : A₀ ⟶ A₁} {v v' : A₀ ⟶ A₂}
    {h : A₁ ⟶ A₃} {k : A₂ ⟶ A₃} (hu : u = u') (hv : v = v') (w : u ≫ h = v ≫ k)
    {w' : u' ≫ h = v' ≫ k} (hc : IsColimit (PushoutCocone.mk h k w')) :
    IsColimit (PushoutCocone.mk h k w) := by
  cases hu
  cases hv
  exact hc

/-- Equal original cospan maps preserve the complete universal property of the same given
projections. -/
def pullbackMkIsLimitOfEq {A₀ A₁ A₂ A₃ : B} {u u' : A₁ ⟶ A₃} {v v' : A₂ ⟶ A₃}
    {h : A₀ ⟶ A₁} {k : A₀ ⟶ A₂} (hu : u = u') (hv : v = v') (w : h ≫ u = k ≫ v)
    {w' : h ≫ u' = k ≫ v'} (hc : IsLimit (PullbackCone.mk h k w')) :
    IsLimit (PullbackCone.mk h k w) := by
  cases hu
  cases hv
  exact hc

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The original canonical latching cocone is retained as a full caller cocone after
postcomposition. -/
abbrev latchingCocone (X : J ⥤ C) : Cocone (r.latchingDiagram (X ⋙ T) j) :=
  T.mapCocone (colimit.cocone (r.latchingDiagram X j))

variable [PreservesColimitsOfShape (r.Latching j) T]

/-- Preserving the actual original boundary makes its image a complete caller latching cocone. -/
def latchingIsColimit (X : J ⥤ C) : IsColimit (latchingCocone r T j X) :=
  isColimitOfPreserves T (colimit.isColimit (r.latchingDiagram X j))

/-- The original complete latching map is unchanged under the caller boundary postcomposition. -/
theorem latchingMapWith_eq (X : J ⥤ C) :
    r.latchingMapWith (X ⋙ T) j (latchingCocone r T j X) (latchingIsColimit r T j X) =
      T.map (latchingMap r X j) := by
  apply (latchingIsColimit r T j X).hom_ext
  intro a
  rw [r.latchingMapWith_ι]
  change T.map (X.map (r.latchingArrow a)) =
    T.map (colimit.ι (r.latchingDiagram X j) a) ≫ T.map (latchingMap r X j)
  rw [← T.map_comp, latchingMap_ι r]

/-- The original natural latching comparison is unchanged under full caller boundary
postcomposition. -/
theorem latchingComparisonWith_eq :
    r.latchingComparisonWith (Functor.whiskerRight f T) j
      (latchingCocone r T j X) (latchingIsColimit r T j X) (latchingCocone r T j Y) =
        T.map (colimMap (r.latchingTransformation f j)) := by
  apply (latchingIsColimit r T j X).hom_ext
  intro a
  rw [r.latchingComparisonWith_ι]
  change T.map (f.app (r.latchingSource a)) ≫ T.map (colimit.ι (r.latchingDiagram Y j) a) =
    T.map (colimit.ι (r.latchingDiagram X j) a) ≫ T.map (colimMap (r.latchingTransformation f j))
  rw [← T.map_comp, ← T.map_comp, ι_colimMap]
  rfl

variable [HasPushouts C]

/-- The image of the actual original pushout is a caller pushout for the postcomposed boundaries. -/
abbrev latchingPushout :
    PushoutCocone
      (r.latchingMapWith (X ⋙ T) j (latchingCocone r T j X) (latchingIsColimit r T j X))
      (r.latchingComparisonWith (Functor.whiskerRight f T) j
        (latchingCocone r T j X) (latchingIsColimit r T j X) (latchingCocone r T j Y)) :=
  PushoutCocone.mk
    (T.map (pushout.inl (latchingMap r X j) (colimMap (r.latchingTransformation f j))))
    (T.map (pushout.inr (latchingMap r X j) (colimMap (r.latchingTransformation f j)))) (by
      calc
        _ = T.map (latchingMap r X j) ≫ T.map (pushout.inl _ _) :=
          congrArg (fun u => u ≫ T.map (pushout.inl _ _)) (latchingMapWith_eq r T j X)
        _ = T.map (latchingMap r X j ≫ pushout.inl _ _) := (T.map_comp _ _).symm
        _ = T.map (colimMap (r.latchingTransformation f j) ≫ pushout.inr _ _) :=
          T.congr_map pushout.condition
        _ = T.map (colimMap (r.latchingTransformation f j)) ≫
          T.map (pushout.inr _ _) := T.map_comp _ _
        _ = _ := congrArg (fun u => u ≫ T.map (pushout.inr _ _))
          (latchingComparisonWith_eq r T f j).symm)

variable [PreservesColimitsOfShape WalkingSpan T]

/-- Preserving the actual original pushout gives its full caller universal property. -/
def latchingPushoutIsColimit : IsColimit (latchingPushout r T f j) := by
  apply pushoutMkIsColimitOfEq (latchingMapWith_eq r T j X) (latchingComparisonWith_eq r T f j)
  exact isColimitOfHasPushoutOfPreservesColimit T (latchingMap r X j)
    (colimMap (r.latchingTransformation f j))

/-- The complete postcomposed caller corner has the image of the original endpoint objects. -/
abbrev latchingChosen :
    T.obj (pushout (latchingMap r X j) (colimMap (r.latchingTransformation f j))) ⟶
      T.obj (Y.obj j) :=
  r.latchingCornerWith (Functor.whiskerRight f T) j
    (latchingCocone r T j X) (latchingIsColimit r T j X)
    (latchingCocone r T j Y) (latchingIsColimit r T j Y)
    (latchingPushout r T f j) (latchingPushoutIsColimit r T f j)

/-- The complete caller corner is the image of the same original latching corner map. -/
theorem latchingChosen_eq : latchingChosen r T f j = T.map (latchingCorner r f j) := by
  apply PushoutCocone.IsColimit.hom_ext (latchingPushoutIsColimit r T f j)
  · rw [r.latchingCornerWith_inl]
    change T.map (f.app j) =
      T.map (pushout.inl (latchingMap r X j) (colimMap (r.latchingTransformation f j))) ≫
        T.map (latchingCorner r f j)
    rw [← T.map_comp, latchingCorner_inl r]
  · rw [r.latchingCornerWith_inr, latchingMapWith_eq]
    change T.map (latchingMap r Y j) =
      T.map (pushout.inr (latchingMap r X j) (colimMap (r.latchingTransformation f j))) ≫
        T.map (latchingCorner r f j)
    rw [← T.map_comp, latchingCorner_inr r]

variable [∀ j, HasColimitsOfShape (r.Latching j) B] [HasPushouts B]

/-- The image of the original latching corner is isomorphic to the actual canonical postcomposed
corner. -/
def latchingArrowIso :
    Arrow.mk (T.map (latchingCorner r f j)) ≅
      Arrow.mk (latchingCorner r (Functor.whiskerRight f T) j) :=
  Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (by
    rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact latchingChosen_eq r T f j) ≪≫
    latchingCornerWithArrowIso r (Functor.whiskerRight f T) j
      (latchingCocone r T j X) (latchingIsColimit r T j X)
      (latchingCocone r T j Y) (latchingIsColimit r T j Y)
      (latchingPushout r T f j) (latchingPushoutIsColimit r T f j)

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The original canonical matching cone is retained as a full caller cone after postcomposition. -/
abbrev matchingCone (X : J ⥤ C) : Cone (r.matchingDiagram (X ⋙ T) j) :=
  T.mapCone (limit.cone (r.matchingDiagram X j))

variable [PreservesLimitsOfShape (r.Matching j) T]

/-- Preserving the actual original boundary makes its image a complete caller matching cone. -/
def matchingIsLimit (X : J ⥤ C) : IsLimit (matchingCone r T j X) :=
  isLimitOfPreserves T (limit.isLimit (r.matchingDiagram X j))

/-- The original complete matching map is unchanged under the caller boundary postcomposition. -/
theorem matchingMapWith_eq (X : J ⥤ C) :
    r.matchingMapWith (X ⋙ T) j (matchingCone r T j X) (matchingIsLimit r T j X) =
      T.map (matchingMap r X j) := by
  apply (matchingIsLimit r T j X).hom_ext
  intro a
  rw [r.matchingMapWith_π]
  change T.map (X.map (r.matchingArrow a)) =
    T.map (matchingMap r X j) ≫ T.map (limit.π (r.matchingDiagram X j) a)
  rw [← T.map_comp, matchingMap_π r]

/-- The original natural matching comparison is unchanged under full caller boundary
postcomposition. -/
theorem matchingComparisonWith_eq :
    r.matchingComparisonWith (Functor.whiskerRight f T) j
      (matchingCone r T j X) (matchingCone r T j Y) (matchingIsLimit r T j Y) =
        T.map (limMap (r.matchingTransformation f j)) := by
  apply (matchingIsLimit r T j Y).hom_ext
  intro a
  rw [r.matchingComparisonWith_π]
  change T.map (limit.π (r.matchingDiagram X j) a) ≫ T.map (f.app (r.matchingTarget a)) =
    T.map (limMap (r.matchingTransformation f j)) ≫ T.map (limit.π (r.matchingDiagram Y j) a)
  rw [← T.map_comp, ← T.map_comp, limMap_π]
  rfl

variable [HasPullbacks C]

/-- The image of the actual original pullback is a caller pullback for the postcomposed
boundaries. -/
abbrev matchingPullback :
    PullbackCone
      (r.matchingComparisonWith (Functor.whiskerRight f T) j
        (matchingCone r T j X) (matchingCone r T j Y) (matchingIsLimit r T j Y))
      (r.matchingMapWith (Y ⋙ T) j (matchingCone r T j Y) (matchingIsLimit r T j Y)) :=
  PullbackCone.mk
    (T.map (pullback.fst (limMap (r.matchingTransformation f j)) (matchingMap r Y j)))
    (T.map (pullback.snd (limMap (r.matchingTransformation f j)) (matchingMap r Y j))) (by
      calc
        _ = T.map (pullback.fst _ _) ≫ T.map (limMap (r.matchingTransformation f j)) :=
          congrArg (fun u => T.map (pullback.fst _ _) ≫ u) (matchingComparisonWith_eq r T f j)
        _ = T.map (pullback.fst _ _ ≫ limMap (r.matchingTransformation f j)) :=
          (T.map_comp _ _).symm
        _ = T.map (pullback.snd _ _ ≫ matchingMap r Y j) := T.congr_map pullback.condition
        _ = T.map (pullback.snd _ _) ≫ T.map (matchingMap r Y j) := T.map_comp _ _
        _ = _ := congrArg (fun u => T.map (pullback.snd _ _) ≫ u) (matchingMapWith_eq r T j Y).symm)

variable [PreservesLimitsOfShape WalkingCospan T]

/-- Preserving the actual original pullback gives its full caller universal property. -/
def matchingPullbackIsLimit : IsLimit (matchingPullback r T f j) := by
  apply pullbackMkIsLimitOfEq (matchingComparisonWith_eq r T f j) (matchingMapWith_eq r T j Y)
  exact isLimitOfHasPullbackOfPreservesLimit T (limMap (r.matchingTransformation f j))
    (matchingMap r Y j)

/-- The complete postcomposed caller corner has the image of the original endpoint objects. -/
abbrev matchingChosen :
    T.obj (X.obj j) ⟶
      T.obj (pullback (limMap (r.matchingTransformation f j)) (matchingMap r Y j)) :=
  r.matchingCornerWith (Functor.whiskerRight f T) j
    (matchingCone r T j X) (matchingIsLimit r T j X)
    (matchingCone r T j Y) (matchingIsLimit r T j Y)
    (matchingPullback r T f j) (matchingPullbackIsLimit r T f j)

/-- The complete caller corner is the image of the same original matching corner map. -/
theorem matchingChosen_eq : matchingChosen r T f j = T.map (matchingCorner r f j) := by
  apply PullbackCone.IsLimit.hom_ext (matchingPullbackIsLimit r T f j)
  · rw [r.matchingCornerWith_fst, matchingMapWith_eq]
    change T.map (matchingMap r X j) =
      T.map (matchingCorner r f j) ≫
        T.map (pullback.fst (limMap (r.matchingTransformation f j)) (matchingMap r Y j))
    rw [← T.map_comp, matchingCorner_fst r]
  · rw [r.matchingCornerWith_snd]
    change T.map (f.app j) =
      T.map (matchingCorner r f j) ≫
        T.map (pullback.snd (limMap (r.matchingTransformation f j)) (matchingMap r Y j))
    rw [← T.map_comp, matchingCorner_snd r]

variable [∀ j, HasLimitsOfShape (r.Matching j) B] [HasPullbacks B]

/-- The image of the original matching corner is isomorphic to the actual canonical postcomposed
corner. -/
def matchingArrowIso :
    Arrow.mk (T.map (matchingCorner r f j)) ≅
      Arrow.mk (matchingCorner r (Functor.whiskerRight f T) j) :=
  Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (by
    rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact matchingChosen_eq r T f j) ≪≫
    matchingCornerWithArrowIso r (Functor.whiskerRight f T) j
      (matchingCone r T j X) (matchingIsLimit r T j X)
      (matchingCone r T j Y) (matchingIsLimit r T j Y)
      (matchingPullback r T f j) (matchingPullbackIsLimit r T f j)

end Matching

end CategoryTheory.ReedyStructure.PostcomposeCorners

end ReedyPart7

section ReedyPart8

open CategoryTheory Limits MorphismProperty


namespace CategoryTheory.ReedyStructure.EvaluationCorners

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  {S : Type uS} [Category.{vS} S] {X Y : J ⥤ S ⥤ C} (f : X ⟶ Y) (s : S) (j : J)

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]

/-- Evaluating the original parameter corner gives the actual original latching corner of the
evaluated map. -/
def latchingArrowIso :
    Arrow.mk ((latchingCorner r f j).app s) ≅
      Arrow.mk (latchingCorner r (Functor.whiskerRight f ((evaluation S C).obj s)) j) :=
  PostcomposeCorners.latchingArrowIso r ((evaluation S C).obj s) f j

/-- Original source class membership is unchanged by the exact parameter latching corner
comparison. -/
theorem latching_mem_iff (P : MorphismProperty C) [P.RespectsIso] :
    P ((latchingCorner r f j).app s) ↔
      P (latchingCorner r (Functor.whiskerRight f ((evaluation S C).obj s)) j) :=
  P.arrow_mk_iso_iff (latchingArrowIso r f s j)

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]

/-- Evaluating the original parameter corner gives the actual original matching corner of the
evaluated map. -/
def matchingArrowIso :
    Arrow.mk ((matchingCorner r f j).app s) ≅
      Arrow.mk (matchingCorner r (Functor.whiskerRight f ((evaluation S C).obj s)) j) :=
  PostcomposeCorners.matchingArrowIso r ((evaluation S C).obj s) f j

/-- Original source class membership is unchanged by the exact parameter matching corner
comparison. -/
theorem matching_mem_iff (P : MorphismProperty C) [P.RespectsIso] :
    P ((matchingCorner r f j).app s) ↔
      P (matchingCorner r (Functor.whiskerRight f ((evaluation S C).obj s)) j) :=
  P.arrow_mk_iso_iff (matchingArrowIso r f s j)

end Matching

end CategoryTheory.ReedyStructure.EvaluationCorners

end ReedyPart8


namespace CategoryTheory.ReedyStructure

open CategoryTheory Limits MorphismProperty

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- Every original diagram retract retains its actual source latching corner class. -/
theorem latchingClass_of_retract
    [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]
    (P : MorphismProperty C) [P.IsStableUnderRetracts]
    {X Y X' Y' : J ⥤ C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : RetractArrow f g) (hg : latchingClass r P g) : latchingClass r P f :=
  MorphismProperty.of_retract h hg

/-- Every original diagram retract retains its actual source matching corner class. -/
theorem matchingClass_of_retract
    [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderRetracts]
    {X Y X' Y' : J ⥤ C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : RetractArrow f g) (hg : matchingClass r P g) : matchingClass r P f :=
  MorphismProperty.of_retract h hg

end CategoryTheory.ReedyStructure

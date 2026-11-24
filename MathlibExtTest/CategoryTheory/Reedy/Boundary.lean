/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uS vS

section OriginalClientPart1

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.ReedyModel.CornerOriginalClients

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  {F G F' G' : J ⥤ C} {f : F ⟶ G} {g : F' ⟶ G'}

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]

/-- Every original natural square keeps both original components and its exact pushout comparison. -/
theorem source_latchingSquare (s : Arrow.mk f ⟶ Arrow.mk g) (j : J) :
    ((r.latchingCornerArrow j).map s).left =
      pushout.map (r.latchingMap F j) (colimMap (r.latchingTransformation f j))
        (r.latchingMap F' j) (colimMap (r.latchingTransformation g j))
        (s.left.app j) (colimMap (r.latchingTransformation s.right j))
        (colimMap (r.latchingTransformation s.left j))
        (r.latchingMap_naturality s.left j) (r.latchingColimMap_square s j) ∧
      ((r.latchingCornerArrow j).map s).right = s.right.app j := ⟨rfl, rfl⟩

/-- The full original square commutes with the actual original latching-corner maps. -/
theorem source_latchingSquare_equation (s : Arrow.mk f ⟶ Arrow.mk g) (j : J) :
    r.latchingCornerSourceMap s j ≫ r.latchingCorner g j = r.latchingCorner f j ≫ s.right.app j :=
  r.latchingCornerSourceMap_corner s j

/-- The original diagram retract supplies an actual retract of the unchanged original latching corners. -/
def source_latchingRetract (h : RetractArrow f g) (j : J) :
    RetractArrow (r.latchingCorner f j) (r.latchingCorner g j) := r.latchingCornerRetract h j

/-- Every original inclusion and retraction component is retained in the full corner retract. -/
theorem source_latchingRetract_components (h : RetractArrow f g) (j : J) :
    (source_latchingRetract r h j).i.left = r.latchingCornerSourceMap h.i j ∧
      (source_latchingRetract r h j).i.right = h.i.right.app j ∧
      (source_latchingRetract r h j).r.left = r.latchingCornerSourceMap h.r j ∧
      (source_latchingRetract r h j).r.right = h.r.right.app j := ⟨rfl, rfl, rfl, rfl⟩

/-- All original inclusion, retraction and splitting equations are retained on the actual latching corners. -/
theorem source_latchingRetract_equations (h : RetractArrow f g) (j : J) :
    r.latchingCornerSourceMap h.i j ≫ r.latchingCorner g j =
      r.latchingCorner f j ≫ h.i.right.app j ∧
      r.latchingCornerSourceMap h.r j ≫ r.latchingCorner f j =
        r.latchingCorner g j ≫ h.r.right.app j ∧
      r.latchingCornerSourceMap h.i j ≫ r.latchingCornerSourceMap h.r j =
        𝟙 (pushout (r.latchingMap F j) (colimMap (r.latchingTransformation f j))) ∧
      h.i.right.app j ≫ h.r.right.app j = 𝟙 (G.obj j) :=
  ⟨r.latchingCornerRetract_i_w h j, r.latchingCornerRetract_r_w h j,
    r.latchingCornerRetract_source h j, CategoryTheory.ReedyStructure.latchingCornerRetract_target h j⟩

/-- The original full Arrow splitting equation is kept, in addition to its coefficient readbacks. -/
theorem source_latchingRetract_arrow (h : RetractArrow f g) (j : J) :
    (r.latchingCornerArrow j).map h.i ≫ (r.latchingCornerArrow j).map h.r =
      𝟙 ((r.latchingCornerArrow j).obj (Arrow.mk f)) := r.latchingCornerRetract_equation h j

/-- Source class retract stability gives the same full original latching-corner condition. -/
theorem source_latchingClass (P : MorphismProperty C) [P.IsStableUnderRetracts]
    (h : RetractArrow f g) (hg : ∀ j : J, P (r.latchingCorner g j)) :
    ∀ j : J, P (r.latchingCorner f j) := CategoryTheory.ReedyStructure.latchingClass_of_retract r P h hg

/-- The derived original latching-corner class exposes its actual retract-stability instance. -/
theorem source_latchingClass_instance (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    (CategoryTheory.ReedyStructure.latchingClass r P).IsStableUnderRetracts := inferInstance

variable [ModelCategory C]

/-- The original model cofibration class is stable under arbitrary original diagram retracts through its corners. -/
theorem source_modelLatchingCofibrations (h : RetractArrow f g)
    (hg : ∀ j : J, cofibrations C (r.latchingCorner g j)) :
    ∀ j : J, cofibrations C (r.latchingCorner f j) :=
  CategoryTheory.ReedyStructure.latchingClass_of_retract r (cofibrations C) h hg

/-- The original model trivial-cofibration class has the same inherited corner retract stability. -/
theorem source_modelLatchingTrivialCofibrations (h : RetractArrow f g)
    (hg : ∀ j : J, trivialCofibrations C (r.latchingCorner g j)) :
    ∀ j : J, trivialCofibrations C (r.latchingCorner f j) :=
  CategoryTheory.ReedyStructure.latchingClass_of_retract r (trivialCofibrations C) h hg

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]

/-- Every original natural square keeps both original components and its exact pullback comparison. -/
theorem source_matchingSquare (s : Arrow.mk f ⟶ Arrow.mk g) (j : J) :
    ((r.matchingCornerArrow j).map s).left = s.left.app j ∧
      ((r.matchingCornerArrow j).map s).right =
        pullback.map (limMap (r.matchingTransformation f j)) (r.matchingMap G j)
          (limMap (r.matchingTransformation g j)) (r.matchingMap G' j)
          (limMap (r.matchingTransformation s.left j)) (s.right.app j)
          (limMap (r.matchingTransformation s.right j))
          (r.matchingLimMap_square s j) (r.matchingMap_naturality s.right j) := ⟨rfl, rfl⟩

/-- The full original square commutes with the actual original matching-corner maps. -/
theorem source_matchingSquare_equation (s : Arrow.mk f ⟶ Arrow.mk g) (j : J) :
    s.left.app j ≫ r.matchingCorner g j = r.matchingCorner f j ≫ r.matchingCornerTargetMap s j :=
  r.matchingCornerTargetMap_corner s j

/-- The original diagram retract supplies an actual retract of the unchanged original matching corners. -/
def source_matchingRetract (h : RetractArrow f g) (j : J) :
    RetractArrow (r.matchingCorner f j) (r.matchingCorner g j) := r.matchingCornerRetract h j

/-- Every original inclusion and retraction component is retained in the full corner retract. -/
theorem source_matchingRetract_components (h : RetractArrow f g) (j : J) :
    (source_matchingRetract r h j).i.left = h.i.left.app j ∧
      (source_matchingRetract r h j).i.right = r.matchingCornerTargetMap h.i j ∧
      (source_matchingRetract r h j).r.left = h.r.left.app j ∧
      (source_matchingRetract r h j).r.right = r.matchingCornerTargetMap h.r j := ⟨rfl, rfl, rfl, rfl⟩

/-- All original inclusion, retraction and splitting equations are retained on the actual matching corners. -/
theorem source_matchingRetract_equations (h : RetractArrow f g) (j : J) :
    h.i.left.app j ≫ r.matchingCorner g j =
      r.matchingCorner f j ≫ r.matchingCornerTargetMap h.i j ∧
      h.r.left.app j ≫ r.matchingCorner f j =
        r.matchingCorner g j ≫ r.matchingCornerTargetMap h.r j ∧
      h.i.left.app j ≫ h.r.left.app j = 𝟙 (F.obj j) ∧
      r.matchingCornerTargetMap h.i j ≫ r.matchingCornerTargetMap h.r j =
        𝟙 (pullback (limMap (r.matchingTransformation f j)) (r.matchingMap G j)) :=
  ⟨r.matchingCornerRetract_i_w h j, r.matchingCornerRetract_r_w h j,
    CategoryTheory.ReedyStructure.matchingCornerRetract_source h j, r.matchingCornerRetract_target h j⟩

/-- The original full Arrow splitting equation is kept, in addition to its coefficient readbacks. -/
theorem source_matchingRetract_arrow (h : RetractArrow f g) (j : J) :
    (r.matchingCornerArrow j).map h.i ≫ (r.matchingCornerArrow j).map h.r =
      𝟙 ((r.matchingCornerArrow j).obj (Arrow.mk f)) := r.matchingCornerRetract_equation h j

/-- Source class retract stability gives the same full original matching-corner condition. -/
theorem source_matchingClass (P : MorphismProperty C) [P.IsStableUnderRetracts]
    (h : RetractArrow f g) (hg : ∀ j : J, P (r.matchingCorner g j)) :
    ∀ j : J, P (r.matchingCorner f j) := CategoryTheory.ReedyStructure.matchingClass_of_retract r P h hg

/-- The derived original matching-corner class exposes its actual retract-stability instance. -/
theorem source_matchingClass_instance (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    (CategoryTheory.ReedyStructure.matchingClass r P).IsStableUnderRetracts := inferInstance

variable [ModelCategory C]

/-- The original model fibration class is stable under arbitrary original diagram retracts through its corners. -/
theorem source_modelMatchingFibrations (h : RetractArrow f g)
    (hg : ∀ j : J, fibrations C (r.matchingCorner g j)) :
    ∀ j : J, fibrations C (r.matchingCorner f j) :=
  CategoryTheory.ReedyStructure.matchingClass_of_retract r (fibrations C) h hg

/-- The original model trivial-fibration class has the same inherited corner retract stability. -/
theorem source_modelMatchingTrivialFibrations (h : RetractArrow f g)
    (hg : ∀ j : J, trivialFibrations C (r.matchingCorner g j)) :
    ∀ j : J, trivialFibrations C (r.matchingCorner f j) :=
  CategoryTheory.ReedyStructure.matchingClass_of_retract r (trivialFibrations C) h hg

end Matching

end HomotopicalAlgebra.ReedyModel.CornerOriginalClients

end OriginalClientPart1

section OriginalClientPart2

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.ReedyModel.OriginalClients

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D]
  (r : CategoryTheory.ReedyStructure J D) {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {F G : J ⥤ C} (f : F ⟶ G)

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The complete original latching corners are recognized without any degree or source-category restriction. -/
theorem source_latchingRecognition :
    (∀ j : J, trivialCofibrations C (r.latchingCorner f j)) ↔
      (∀ j : J, cofibrations C (r.latchingCorner f j)) ∧
      (∀ j : J, weakEquivalences C (f.app j)) :=
  latchingCorner_trivialCofibrations_iff r f

/-- The original scalar square has its full chosen-cocone lift constructed only from source model lifting. -/
def source_latchingSquareLift (j : J)
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    {U V : C} (p : U ⟶ V) {t : cX.pt ⟶ U} {b : cY.pt ⟶ V}
    (sq : CommSq t (r.latchingComparisonWith f j cX hX cY) p b)
    (hp : fibrations C p)
    (hc : ∀ k : J, r.degree k < r.degree j → trivialCofibrations C (r.latchingCorner f k)) :
    sq.LiftStruct :=
  r.latchingComparisonWithLiftStruct f j cX hX cY hY p sq
    (fun k hk => hasLiftingProperty_of_wfs _ _ (hc k hk) hp)

/-- Both original caller maps of the scalar square are retained by the constructed latching lift. -/
theorem source_latchingSquare_factors (j : J)
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    {U V : C} (p : U ⟶ V) {t : cX.pt ⟶ U} {b : cY.pt ⟶ V}
    (sq : CommSq t (r.latchingComparisonWith f j cX hX cY) p b)
    (hp : fibrations C p)
    (hc : ∀ k : J, r.degree k < r.degree j → trivialCofibrations C (r.latchingCorner f k)) :
    r.latchingComparisonWith f j cX hX cY ≫
      (source_latchingSquareLift r f j cX hX cY hY p sq hp hc).l = t ∧
      (source_latchingSquareLift r f j cX hX cY hY p sq hp hc).l ≫ p = b :=
  ⟨(source_latchingSquareLift r f j cX hX cY hY p sq hp hc).fac_left,
    (source_latchingSquareLift r f j cX hX cY hY p sq hp hc).fac_right⟩

/-- Every original chosen latching-corner component is the canonical component under the complete comparison. -/
theorem source_latchingCorner_comparison (j : J)
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) :
    (r.latchingCornerSourceIso f j cX hX cY hY cP hP).hom ≫ r.latchingCorner f j =
      r.latchingCornerWith f j cX hX cY hY cP hP :=
  r.latchingCornerWith_comparison f j cX hX cY hY cP hP

/-- Full families of original caller chosen cocones and pushouts have the same source recognition. -/
theorem source_chosenLatchingRecognition
    (cX : ∀ j : J, Cocone (r.latchingDiagram F j)) (hX : ∀ j : J, IsColimit (cX j))
    (cY : ∀ j : J, Cocone (r.latchingDiagram G j)) (hY : ∀ j : J, IsColimit (cY j))
    (cP : ∀ j : J, PushoutCocone (r.latchingMapWith F j (cX j) (hX j))
      (r.latchingComparisonWith f j (cX j) (hX j) (cY j)))
    (hP : ∀ j : J, IsColimit (cP j)) :
    (∀ j : J, trivialCofibrations C
      (r.latchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ↔
      (∀ j : J, cofibrations C
        (r.latchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ∧
      (∀ j : J, weakEquivalences C (f.app j)) :=
  latchingCornerWith_trivialCofibrations_iff r f cX hX cY hY cP hP

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The complete original matching corners are recognized without any degree or source-category restriction. -/
theorem source_matchingRecognition :
    (∀ j : J, trivialFibrations C (r.matchingCorner f j)) ↔
      (∀ j : J, fibrations C (r.matchingCorner f j)) ∧
      (∀ j : J, weakEquivalences C (f.app j)) :=
  matchingCorner_trivialFibrations_iff r f

/-- The original scalar square has its full chosen-cone lift constructed only from source model lifting. -/
def source_matchingSquareLift (j : J)
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    {U V : C} (i : U ⟶ V) {t : U ⟶ cX.pt} {b : V ⟶ cY.pt}
    (sq : CommSq t i (r.matchingComparisonWith f j cX cY hY) b)
    (hi : cofibrations C i)
    (hc : ∀ k : J, r.degree k < r.degree j → trivialFibrations C (r.matchingCorner f k)) :
    sq.LiftStruct :=
  r.matchingComparisonWithLiftStruct f j cX hX cY hY i sq
    (fun k hk => hasLiftingProperty_of_wfs _ _ hi (hc k hk))

/-- Both original caller maps of the scalar square are retained by the constructed matching lift. -/
theorem source_matchingSquare_factors (j : J)
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    {U V : C} (i : U ⟶ V) {t : U ⟶ cX.pt} {b : V ⟶ cY.pt}
    (sq : CommSq t i (r.matchingComparisonWith f j cX cY hY) b)
    (hi : cofibrations C i)
    (hc : ∀ k : J, r.degree k < r.degree j → trivialFibrations C (r.matchingCorner f k)) :
    i ≫ (source_matchingSquareLift r f j cX hX cY hY i sq hi hc).l = t ∧
      (source_matchingSquareLift r f j cX hX cY hY i sq hi hc).l ≫
        r.matchingComparisonWith f j cX cY hY = b :=
  ⟨(source_matchingSquareLift r f j cX hX cY hY i sq hi hc).fac_left,
    (source_matchingSquareLift r f j cX hX cY hY i sq hi hc).fac_right⟩

/-- Every original chosen matching-corner component is the canonical component under the complete comparison. -/
theorem source_matchingCorner_comparison (j : J)
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY))
    (hP : IsLimit cP) :
    r.matchingCornerWith f j cX hX cY hY cP hP ≫
      (r.matchingCornerTargetIso f j cX hX cY hY cP hP).hom = r.matchingCorner f j :=
  r.matchingCornerWith_comparison f j cX hX cY hY cP hP

/-- Full families of original caller chosen cones and pullbacks have the same source recognition. -/
theorem source_chosenMatchingRecognition
    (cX : ∀ j : J, Cone (r.matchingDiagram F j)) (hX : ∀ j : J, IsLimit (cX j))
    (cY : ∀ j : J, Cone (r.matchingDiagram G j)) (hY : ∀ j : J, IsLimit (cY j))
    (cP : ∀ j : J, PullbackCone (r.matchingComparisonWith f j (cX j) (cY j) (hY j))
      (r.matchingMapWith G j (cY j) (hY j)))
    (hP : ∀ j : J, IsLimit (cP j)) :
    (∀ j : J, trivialFibrations C
      (r.matchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ↔
      (∀ j : J, fibrations C
        (r.matchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ∧
      (∀ j : J, weakEquivalences C (f.app j)) :=
  matchingCornerWith_trivialFibrations_iff r f cX hX cY hY cP hP

end Matching

end HomotopicalAlgebra.ReedyModel.OriginalClients

end OriginalClientPart2

section OriginalClientPart3

open CategoryTheory MorphismProperty

namespace CategoryTheory.ReedyStructure.PrefixGluing.OriginalClients

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C} (f : X ⟶ Y)

section Lower

variable (d : D) (a : ∀ e : D, e < d → PrefixFactor r f e)
  (h : ∀ (e e' : D) (he : e < d) (he' : e' < d) (hle : e ≤ e'),
    (a e' he').Extends (a e he) hle)

/-- The complete factor lives on the actual original strict lower source. -/
def source_lowerFactor : MapFactorizationData (⊤ : MorphismProperty (r.Below d ⥤ C)) ⊤
    (Functor.whiskerLeft (r.belowObjects d).ι f) := lowerFactor r f d a h

/-- Every original source coefficient record is retained literally from any adequate caller prefix. -/
theorem source_lowerCoefficient (j : J) (hj : r.degree j < d)
    (e : D) (he : e < d) (hje : r.degree j ≤ e) :
    coefficient (source_lowerFactor r f d a h) (⟨j, hj⟩ : r.Below d) = (a e he).component j hje :=
  lowerFactor_coefficient r f d a h j hj e he hje

/-- Every original intermediate lower arrow is the same caller prefix arrow. -/
theorem source_lowerMap (i j : J) (hi : r.degree i < d) (hj : r.degree j < d) (g : i ⟶ j)
    (e : D) (he : e < d) (hie : r.degree i ≤ e) (hje : r.degree j ≤ e) :
    HEq ((source_lowerFactor r f d a h).Z.map
      (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Below d) ⟶ ⟨j, hj⟩)) ((a e he).map i j hie hje g) :=
  lowerFactor_map_heq r f d a h i j hi hj g e he hie hje

/-- Both unchanged original lower factor components are retained from every adequate prefix. -/
theorem source_lowerFactors (j : J) (hj : r.degree j < d)
    (e : D) (he : e < d) (hje : r.degree j ≤ e) :
    HEq ((source_lowerFactor r f d a h).i.app (⟨j, hj⟩ : r.Below d)) ((a e he).component j hje).i ∧
      HEq ((source_lowerFactor r f d a h).p.app (⟨j, hj⟩ : r.Below d)) ((a e he).component j hje).p := by
  have hc := source_lowerCoefficient r f d a h j hj e he hje
  have hi : HEq (coefficient (source_lowerFactor r f d a h) ⟨j, hj⟩).i
      ((a e he).component j hje).i :=
    Eq.mp (congrArg (fun c => HEq (coefficient (source_lowerFactor r f d a h) ⟨j, hj⟩).i c.i) hc) HEq.rfl
  have hp : HEq (coefficient (source_lowerFactor r f d a h) ⟨j, hj⟩).p
      ((a e he).component j hje).p :=
    Eq.mp (congrArg (fun c => HEq (coefficient (source_lowerFactor r f d a h) ⟨j, hj⟩).p c.p) hc) HEq.rfl
  exact ⟨hi, hp⟩

/-- Every original lower source arrow retains both natural factor squares. -/
theorem source_lowerNaturality (i j : J) (hi : r.degree i < d) (hj : r.degree j < d) (g : i ⟶ j) :
    X.map g ≫ (source_lowerFactor r f d a h).i.app (⟨j, hj⟩ : r.Below d) =
      (source_lowerFactor r f d a h).i.app (⟨i, hi⟩ : r.Below d) ≫
        (source_lowerFactor r f d a h).Z.map
          (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Below d) ⟶ ⟨j, hj⟩) ∧
      (source_lowerFactor r f d a h).Z.map
        (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Below d) ⟶ ⟨j, hj⟩) ≫
        (source_lowerFactor r f d a h).p.app (⟨j, hj⟩ : r.Below d) =
        (source_lowerFactor r f d a h).p.app (⟨i, hi⟩ : r.Below d) ≫ Y.map g :=
  ⟨(source_lowerFactor r f d a h).i.naturality
      (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Below d) ⟶ ⟨j, hj⟩),
    (source_lowerFactor r f d a h).p.naturality
      (ObjectProperty.homMk g : (⟨i, hi⟩ : r.Below d) ⟶ ⟨j, hj⟩)⟩

/-- The same complete lower factors multiply to the unchanged original restricted source map. -/
theorem source_lowerEquation : (source_lowerFactor r f d a h).i ≫ (source_lowerFactor r f d a h).p =
    Functor.whiskerLeft (r.belowObjects d).ι f := (source_lowerFactor r f d a h).fac

end Lower

section Full

variable (a : ∀ d : D, PrefixFactor r f d)
  (h : ∀ (d e : D) (hle : e ≤ d), (a d).Extends (a e) hle)

/-- The complete factor lives on all original J objects and all original J arrows. -/
def source_fullFactor : MapFactorizationData (⊤ : MorphismProperty (J ⥤ C)) ⊤ f := fullFactor r f a h

/-- Every full original source coefficient record is retained literally from any adequate caller prefix. -/
theorem source_fullCoefficient (j : J) (d : D) (hj : r.degree j ≤ d) :
    coefficient (source_fullFactor r f a h) j = (a d).component j hj :=
  fullFactor_coefficient r f a h j d hj

/-- Every original intermediate full arrow is the same caller prefix arrow. -/
theorem source_fullMap (i j : J) (g : i ⟶ j) (d : D) (hi : r.degree i ≤ d) (hj : r.degree j ≤ d) :
    HEq ((source_fullFactor r f a h).Z.map g) ((a d).map i j hi hj g) :=
  fullFactor_map_heq r f a h i j g d hi hj

/-- Both unchanged original full factor components are retained from every adequate prefix. -/
theorem source_fullFactors (j : J) (d : D) (hj : r.degree j ≤ d) :
    HEq ((source_fullFactor r f a h).i.app j) ((a d).component j hj).i ∧
      HEq ((source_fullFactor r f a h).p.app j) ((a d).component j hj).p := by
  have hc := source_fullCoefficient r f a h j d hj
  have hi : HEq (coefficient (source_fullFactor r f a h) j).i ((a d).component j hj).i :=
    Eq.mp (congrArg (fun c => HEq (coefficient (source_fullFactor r f a h) j).i c.i) hc) HEq.rfl
  have hp : HEq (coefficient (source_fullFactor r f a h) j).p ((a d).component j hj).p :=
    Eq.mp (congrArg (fun c => HEq (coefficient (source_fullFactor r f a h) j).p c.p) hc) HEq.rfl
  exact ⟨hi, hp⟩

/-- Every original full source arrow retains both natural factor squares. -/
theorem source_fullNaturality (i j : J) (g : i ⟶ j) :
    X.map g ≫ (source_fullFactor r f a h).i.app j =
      (source_fullFactor r f a h).i.app i ≫ (source_fullFactor r f a h).Z.map g ∧
      (source_fullFactor r f a h).Z.map g ≫ (source_fullFactor r f a h).p.app j =
        (source_fullFactor r f a h).p.app i ≫ Y.map g :=
  ⟨(source_fullFactor r f a h).i.naturality g, (source_fullFactor r f a h).p.naturality g⟩

/-- The same complete full factors multiply to the unchanged original natural transformation. -/
theorem source_fullEquation : (source_fullFactor r f a h).i ≫ (source_fullFactor r f a h).p = f :=
  (source_fullFactor r f a h).fac

end Full

end CategoryTheory.ReedyStructure.PrefixGluing.OriginalClients

end OriginalClientPart3

section OriginalClientPart4

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.StageCorners.OriginalClients

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y) {d : D}
  (L : MapFactorizationData (⊤ : MorphismProperty (r.Below d ⥤ C)) ⊤
    (Functor.whiskerLeft (r.belowObjects d).ι f))
  {P Q : MorphismProperty C} (F : FactorizationData P Q)

/-- The new-degree original latching corner is the actual original coefficient factory left arrow. -/
def new_latching (j : J) (hj : r.degree j = d) :
    Arrow.mk ((r.throughStructure d).latchingCorner (StageFactory.nextPrefix r f L F).i
      (⟨j, le_of_eq hj⟩ : r.Through d)) ≅ Arrow.mk ((StageFactory.coefficientFactor r f L F j hj).i) :=
  latchingArrowIsoNew r f L F ⟨j, le_of_eq hj⟩ hj

/-- The new-degree original matching corner is the actual original coefficient factory right arrow. -/
def new_matching (j : J) (hj : r.degree j = d) :
    Arrow.mk ((r.throughStructure d).matchingCorner (StageFactory.nextPrefix r f L F).p
      (⟨j, le_of_eq hj⟩ : r.Through d)) ≅ Arrow.mk ((StageFactory.coefficientFactor r f L F j hj).p) :=
  matchingArrowIsoNew r f L F ⟨j, le_of_eq hj⟩ hj

/-- The old-degree original latching corner is the actual original lower factor corner. -/
def old_latching (j : J) (hj : r.degree j < d) :
    Arrow.mk ((r.throughStructure d).latchingCorner (StageFactory.nextPrefix r f L F).i
      (⟨j, le_of_lt hj⟩ : r.Through d)) ≅
      Arrow.mk ((r.belowStructure d).latchingCorner L.i (⟨j, hj⟩ : r.Below d)) :=
  latchingArrowIsoOld r f L F ⟨j, le_of_lt hj⟩ hj

/-- The old-degree original matching corner is the actual original lower factor corner. -/
def old_matching (j : J) (hj : r.degree j < d) :
    Arrow.mk ((r.throughStructure d).matchingCorner (StageFactory.nextPrefix r f L F).p
      (⟨j, le_of_lt hj⟩ : r.Through d)) ≅
      Arrow.mk ((r.belowStructure d).matchingCorner L.p (⟨j, hj⟩ : r.Below d)) :=
  matchingArrowIsoOld r f L F ⟨j, le_of_lt hj⟩ hj

/-- The actual new-degree latching comparison keeps the unchanged original factory left map in its full square. -/
theorem new_latching_square (j : J) (hj : r.degree j = d) :
    (new_latching r f L F j hj).hom.left ≫ (StageFactory.coefficientFactor r f L F j hj).i =
      (r.throughStructure d).latchingCorner (StageFactory.nextPrefix r f L F).i
        (⟨j, le_of_eq hj⟩ : r.Through d) ≫ (new_latching r f L F j hj).hom.right :=
  (new_latching r f L F j hj).hom.w

/-- The actual new-degree matching comparison keeps the unchanged original factory right map in its full square. -/
theorem new_matching_square (j : J) (hj : r.degree j = d) :
    (new_matching r f L F j hj).hom.left ≫ (StageFactory.coefficientFactor r f L F j hj).p =
      (r.throughStructure d).matchingCorner (StageFactory.nextPrefix r f L F).p
        (⟨j, le_of_eq hj⟩ : r.Through d) ≫ (new_matching r f L F j hj).hom.right :=
  (new_matching r f L F j hj).hom.w

/-- The original new-degree latching Arrow comparison retains both inverse equations. -/
theorem new_latching_inverses (j : J) (hj : r.degree j = d) :
    (new_latching r f L F j hj).hom ≫ (new_latching r f L F j hj).inv =
      𝟙 (Arrow.mk ((r.throughStructure d).latchingCorner (StageFactory.nextPrefix r f L F).i
        (⟨j, le_of_eq hj⟩ : r.Through d))) ∧
      (new_latching r f L F j hj).inv ≫ (new_latching r f L F j hj).hom =
        𝟙 (Arrow.mk ((StageFactory.coefficientFactor r f L F j hj).i)) :=
  ⟨(new_latching r f L F j hj).hom_inv_id, (new_latching r f L F j hj).inv_hom_id⟩

/-- The original new-degree matching Arrow comparison retains both inverse equations. -/
theorem new_matching_inverses (j : J) (hj : r.degree j = d) :
    (new_matching r f L F j hj).hom ≫ (new_matching r f L F j hj).inv =
      𝟙 (Arrow.mk ((r.throughStructure d).matchingCorner (StageFactory.nextPrefix r f L F).p
        (⟨j, le_of_eq hj⟩ : r.Through d))) ∧
      (new_matching r f L F j hj).inv ≫ (new_matching r f L F j hj).hom =
        𝟙 (Arrow.mk ((StageFactory.coefficientFactor r f L F j hj).p)) :=
  ⟨(new_matching r f L F j hj).hom_inv_id, (new_matching r f L F j hj).inv_hom_id⟩

/-- Every original new-degree incoming cone leg keeps its exact old object transport and original injection. -/
theorem latching_leg (j : J) (hj : r.degree j = d)
    (a : (r.throughStructure d).Latching (⟨j, le_of_eq hj⟩ : r.Through d)) :
    (StageCornerMaps.nextLatchingCocone r f L F ⟨j, le_of_eq hj⟩).ι.app a =
      (StageCornerMaps.oldObjIso r f L F ((r.throughStructure d).latchingSource a)
        (StageBoundaryCones.latchingSource_lt r ⟨j, le_of_eq hj⟩ a)).hom ≫
        colimit.ι (StageBoundaryCones.lowerLatchingAt r L.Z ⟨j, le_of_eq hj⟩)
          ((StageBoundaryCones.throughLatching r ⟨j, le_of_eq hj⟩).functor.obj a) :=
  StageCornerMaps.nextLatchingCocone_ι r f L F ⟨j, le_of_eq hj⟩ a

/-- Every original new-degree outgoing cone leg keeps its original projection and inverse old object transport. -/
theorem matching_leg (j : J) (hj : r.degree j = d)
    (a : (r.throughStructure d).Matching (⟨j, le_of_eq hj⟩ : r.Through d)) :
    (StageCornerMaps.nextMatchingCone r f L F ⟨j, le_of_eq hj⟩).π.app a =
      limit.π (StageBoundaryCones.lowerMatchingAt r L.Z ⟨j, le_of_eq hj⟩)
        ((StageBoundaryCones.throughMatching r ⟨j, le_of_eq hj⟩).functor.obj a) ≫
        (StageCornerMaps.oldObjIso r f L F ((r.throughStructure d).matchingTarget a)
          (StageBoundaryCones.matchingTarget_lt r ⟨j, le_of_eq hj⟩ a)).inv :=
  StageCornerMaps.nextMatchingCone_π r f L F ⟨j, le_of_eq hj⟩ a

/-- The original factory left map remains literal under the chosen corner endpoint comparison. -/
theorem factory_left_readback (j : J) (hj : r.degree j = d) :
    latchingChosen r f L F (⟨j, le_of_eq hj⟩ : r.Through d) ≫
      (StageCornerMaps.newObjIso r f L F ⟨j, le_of_eq hj⟩ hj).hom =
      (StageFactory.coefficientFactor r f L F j hj).i :=
  latchingChosen_new r f L F ⟨j, le_of_eq hj⟩ hj

/-- The original factory right map remains literal under the chosen corner endpoint comparison. -/
theorem factory_right_readback (j : J) (hj : r.degree j = d) :
    matchingChosen r f L F (⟨j, le_of_eq hj⟩ : r.Through d) =
      (StageCornerMaps.newObjIso r f L F ⟨j, le_of_eq hj⟩ hj).hom ≫
        (StageFactory.coefficientFactor r f L F j hj).p :=
  matchingChosen_new r f L F ⟨j, le_of_eq hj⟩ hj

/-- The actual source factory and unchanged lower latching classes give all actual next-prefix left corners. -/
theorem source_left_classes [P.RespectsIso]
    (hL : ∀ j : r.Below d, P ((r.belowStructure d).latchingCorner L.i j)) :
    ∀ j : r.Through d, P ((r.throughStructure d).latchingCorner (StageFactory.nextPrefix r f L F).i j) :=
  latching_mem_all r f L F hL

/-- The actual source factory and unchanged lower matching classes give all actual next-prefix right corners. -/
theorem source_right_classes [Q.RespectsIso]
    (hL : ∀ j : r.Below d, Q ((r.belowStructure d).matchingCorner L.p j)) :
    ∀ j : r.Through d, Q ((r.throughStructure d).matchingCorner (StageFactory.nextPrefix r f L F).p j) :=
  matching_mem_all r f L F hL

end CategoryTheory.ReedyStructure.StageCorners.OriginalClients

namespace CategoryTheory.ReedyStructure.RestrictionCorners.OriginalClients

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C} (f : X ⟶ Y) {d : D}

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]

/-- The full original corner and its bounded restriction retain the same Arrow type on all original variables. -/
def latching (j : J) (hj : r.degree j ≤ d) :
    Arrow.mk (r.latchingCorner f j) ≅ Arrow.mk ((r.throughStructure d).latchingCorner
      (Functor.whiskerLeft (r.throughObjects d).ι f) (⟨j, hj⟩ : r.Through d)) :=
  latchingArrowIso r f ⟨j, hj⟩

theorem latching_classes (R : MorphismProperty C) [R.RespectsIso] (j : J) (hj : r.degree j ≤ d) :
    R (r.latchingCorner f j) ↔ R ((r.throughStructure d).latchingCorner
      (Functor.whiskerLeft (r.throughObjects d).ι f) (⟨j, hj⟩ : r.Through d)) :=
  latching_mem_iff r f R ⟨j, hj⟩

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]

/-- The full original matching corner and its bounded restriction retain the same Arrow type. -/
def matching (j : J) (hj : r.degree j ≤ d) :
    Arrow.mk (r.matchingCorner f j) ≅ Arrow.mk ((r.throughStructure d).matchingCorner
      (Functor.whiskerLeft (r.throughObjects d).ι f) (⟨j, hj⟩ : r.Through d)) :=
  matchingArrowIso r f ⟨j, hj⟩

theorem matching_classes (R : MorphismProperty C) [R.RespectsIso] (j : J) (hj : r.degree j ≤ d) :
    R (r.matchingCorner f j) ↔ R ((r.throughStructure d).matchingCorner
      (Functor.whiskerLeft (r.throughObjects d).ι f) (⟨j, hj⟩ : r.Through d)) :=
  matching_mem_iff r f R ⟨j, hj⟩

end Matching

end CategoryTheory.ReedyStructure.RestrictionCorners.OriginalClients

end OriginalClientPart4

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.FramingHomotopy
public import MathlibExt.AlgebraicTopology.ModelCategory.FramingCoefficientFactory
public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplexCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplexCategory.ReedyComparison
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Const
public import MathlibExt.CategoryTheory.Reedy.FactorizationCorners
public import MathlibExt.CategoryTheory.Reedy.DegreeZero
public import MathlibExt.CategoryTheory.Reedy.Corner

/-!
# Functorial framings from the actual chosen factorization data

One degree construction uses the original Q/R endpoints and the supplied
cofibration/fibration factories. All factors, degree-zero maps, augmentations,
latching/matching data and weak-constancy laws retain those original choices.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC
open CategoryTheory Limits MorphismProperty Simplicial

namespace HomotopicalAlgebra.FunctorialFramings

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

namespace FrameEndpoints
open FramingEndpoints
/-- The same original chosen Q functor acts on every cosimplicial endpoint diagram. -/
abbrev originalLeft : C ⥤ CosimplicialObject C := d.Q ⋙ leftFree

/-- The same original chosen R functor acts on every simplicial endpoint diagram. -/
abbrev originalRight : C ⥤ SimplicialObject C := d.R ⋙ rightFree

/-- Every original Q object is retained as the coefficient of the left endpoint diagram. -/
theorem originalLeft_obj (X : C) : (originalLeft d).obj X = leftFree.obj (d.Q.obj X) := rfl

/-- Every original Q map is retained as the whole left endpoint diagram map. -/
theorem originalLeft_map {X Y : C} (f : X ⟶ Y) :
    (originalLeft d).map f = leftFree.map (d.Q.map f) := rfl

/-- Every original R object is retained as the coefficient of the right endpoint diagram. -/
theorem originalRight_obj (X : C) : (originalRight d).obj X = rightFree.obj (d.R.obj X) := rfl

/-- Every original R map is retained as the whole right endpoint diagram map. -/
theorem originalRight_map {X Y : C} (f : X ⟶ Y) :
    (originalRight d).map f = rightFree.map (d.R.map f) := rfl

/-- The original whole fold is restricted along the same original chosen Q. -/
def originalCosimplicialFold : originalLeft d ⟶ d.Q ⋙ CosimplicialObject.const C :=
  Functor.whiskerLeft d.Q cosimplicialFold

/-- The original whole diagonal is restricted along the same original chosen R. -/
def originalSimplicialDiagonal : d.R ⋙ SimplicialObject.const C ⟶ originalRight d :=
  Functor.whiskerLeft d.R simplicialDiagonal

/-- The left chosen endpoint in degree zero retains the same original Q functor. -/
def originalLeftZeroIso : originalLeft d ⋙ (evaluation SimplexCategory C).obj ⦋0⦌ ≅ d.Q :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft d.Q leftDegreeZeroIso ≪≫ Functor.rightUnitor _

/-- The right chosen endpoint in degree zero retains the same original R functor. -/
def originalRightZeroIso :
    originalRight d ⋙ (evaluation SimplexCategoryᵒᵖ C).obj (Opposite.op ⦋0⦌) ≅ d.R :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft d.R rightDegreeZeroIso ≪≫ Functor.rightUnitor _

/-- The chosen left degree-zero isomorphism is the unchanged original Q fold. -/
theorem originalLeftZeroIso_hom (X : C) :
    (originalLeftZeroIso d).hom.app X =
      ((cosimplicialFold (C := C)).app (d.Q.obj X)).app ⦋0⦌ := by
  simp [originalLeftZeroIso, leftDegreeZeroIso_hom]

/-- The chosen right degree-zero inverse is the unchanged original d.Riagonal. -/
theorem originalRightZeroIso_inv (X : C) :
    (originalRightZeroIso d).inv.app X =
      ((simplicialDiagonal (C := C)).app (d.R.obj X)).app (Opposite.op ⦋0⦌) := by
  simp [originalRightZeroIso, rightDegreeZeroIso_inv]


end FrameEndpoints

/-- The unchanged original chosen-Q fold, with its parameter and degree variables flipped. -/
def leftEndpointArrow : (FrameEndpoints.originalLeft d).flip ⟶
    (d.Q ⋙ CosimplicialObject.const C).flip :=
  (flipFunctor C SimplexCategory C).map (FrameEndpoints.originalCosimplicialFold d)

/-- The unchanged original generated-d.Riagonal, with its parameter and degree variables flipped. -/
def rightEndpointArrow : (d.R ⋙ SimplicialObject.const C).flip ⟶
    (FrameEndpoints.originalRight d).flip :=
  (flipFunctor C SimplexCategoryᵒᵖ C).map (FrameEndpoints.originalSimplicialDiagonal d)

/-- The actual complete original I degree factorization of the chosen-Q fold. -/
def leftFactor :
    MapFactorizationData
      (ReedyStructure.latchingClass SimplexCategory.reedy
        ((cofibrations C).functorCategory C))
      (ReedyStructure.matchingClass SimplexCategory.reedy
        ((trivialFibrations C).functorCategory C)) (leftEndpointArrow d) :=
  ReedyStructure.DegreeFactorization.classifiedFactor SimplexCategory.reedy
    (leftEndpointArrow d) (fun {_ _} f ↦ FramingCoefficientFactory.cofibrant d.cofibrantFactor f)

/-- The actual complete original J degree factorization of the generated-d.Riagonal. -/
def rightFactor :
    MapFactorizationData
      (ReedyStructure.latchingClass SimplexCategory.reedyOp
        ((trivialCofibrations C).functorCategory C))
      (ReedyStructure.matchingClass SimplexCategory.reedyOp
        ((fibrations C).functorCategory C)) (rightEndpointArrow d) :=
  ReedyStructure.DegreeFactorization.classifiedFactor SimplexCategory.reedyOp
    (rightEndpointArrow d) (fun {_ _} f ↦ FramingCoefficientFactory.fibrant d.fibrantFactor f)

/-- The actual original I-factor middle diagrams as a functor of every original object and map. -/
def leftFrame : C ⥤ CosimplicialObject C := (leftFactor d).Z.flip

/-- The actual original J-factor middle diagrams as a functor of every original object and map. -/
def rightFrame : C ⥤ SimplicialObject C := (rightFactor d).Z.flip

/-- The actual whole original I source factor into the cosimplicial middle diagram. -/
def fromLeftFree : FrameEndpoints.originalLeft d ⟶ leftFrame d :=
  (flipFunctor SimplexCategory C C).map (leftFactor d).i

/-- The actual whole original I target factor to the same original chosen Q. -/
def leftResolution : leftFrame d ⟶ d.Q ⋙ CosimplicialObject.const C :=
  (flipFunctor SimplexCategory C C).map (leftFactor d).p

/-- The actual whole original J source factor from the same original chosen R. -/
def rightResolution : d.R ⋙ SimplicialObject.const C ⟶ rightFrame d :=
  (flipFunctor SimplexCategoryᵒᵖ C C).map (rightFactor d).i

/-- The actual whole original J target factor to the original finite-power endpoint. -/
def toRightFree : rightFrame d ⟶ FrameEndpoints.originalRight d :=
  (flipFunctor SimplexCategoryᵒᵖ C C).map (rightFactor d).p

/-- Both actual I factors recover the unchanged original chosen-Q fold. -/
theorem left_fac : fromLeftFree d ≫ leftResolution d =
    FrameEndpoints.originalCosimplicialFold d := by
  change (flipFunctor SimplexCategory C C).map (leftFactor d).i ≫
    (flipFunctor SimplexCategory C C).map (leftFactor d).p = _
  rw [← CategoryTheory.Functor.map_comp, (leftFactor d).fac]
  rfl

/-- Both actual J factors recover the unchanged original generated-d.Riagonal. -/
theorem right_fac : rightResolution d ≫ toRightFree d =
    FrameEndpoints.originalSimplicialDiagonal d := by
  change (flipFunctor SimplexCategoryᵒᵖ C C).map (rightFactor d).i ≫
    (flipFunctor SimplexCategoryᵒᵖ C C).map (rightFactor d).p = _
  rw [← CategoryTheory.Functor.map_comp, (rightFactor d).fac]
  rfl

/-- The original chosen-Q endpoint coefficient is a whole natural isomorphism in degree zero. -/
instance leftEndpointArrow_zero_isIso : IsIso ((leftEndpointArrow d).app ⦋0⦌) := by
  have h : (leftEndpointArrow d).app ⦋0⦌ = (FrameEndpoints.originalLeftZeroIso d).hom := by
    apply NatTrans.ext
    funext X
    exact (FrameEndpoints.originalLeftZeroIso_hom d X).symm
  rw [h]
  infer_instance

/-- The original chosen-R endpoint coefficient is a whole natural isomorphism in degree zero. -/
instance rightEndpointArrow_zero_isIso :
    IsIso ((rightEndpointArrow d).app (Opposite.op ⦋0⦌)) := by
  have h : (rightEndpointArrow d).app (Opposite.op ⦋0⦌) =
      (FrameEndpoints.originalRightZeroIso d).inv := by
    apply NatTrans.ext
    funext X
    exact (FrameEndpoints.originalRightZeroIso_inv d X).symm
  rw [h]
  infer_instance

/-- The actual global I right factor keeps the original Q endpoint in degree zero. -/
instance leftFactor_zero_p_isIso : IsIso ((leftFactor d).p.app ⦋0⦌) :=
  ReedyStructure.DegreeFactorization.normalizedTarget_factor_p_isIso_at_bot
    SimplexCategory.reedy (leftEndpointArrow d)
    (fun {_ _} f ↦ ((d.cofibrantFactor).functorCategory C).factorizationData f)
    ⦋0⦌ rfl

/-- The actual global J left factor keeps the original R endpoint in degree zero. -/
instance rightFactor_zero_i_isIso : IsIso ((rightFactor d).i.app (Opposite.op ⦋0⦌)) :=
  ReedyStructure.DegreeFactorization.normalizedSource_factor_i_isIso_at_bot
    SimplexCategory.reedyOp (rightEndpointArrow d)
    (fun {_ _} f ↦ ((d.fibrantFactor).functorCategory C).factorizationData f)
    (Opposite.op ⦋0⦌) rfl

/-- The actual cosimplicial degree-zero middle is naturally the same original chosen Q. -/
def leftZeroIso : leftFrame d ⋙ (evaluation SimplexCategory C).obj ⦋0⦌ ≅ d.Q :=
  CategoryTheory.flipCompEvaluation (leftFactor d).Z ⦋0⦌ ≪≫
    @asIso (C ⥤ C) _ _ _ ((leftFactor d).p.app ⦋0⦌) (leftFactor_zero_p_isIso d) ≪≫
      (show (d.Q ⋙ Functor.const SimplexCategory).flip.obj ⦋0⦌ ≅ d.Q
        from Iso.refl d.Q)

/-- The same original chosen R naturally identifies the actual simplicial degree-zero middle. -/
def rightZeroIso : d.R ≅ rightFrame d ⋙
    (evaluation SimplexCategoryᵒᵖ C).obj (Opposite.op ⦋0⦌) :=
  (show (d.R ⋙ Functor.const SimplexCategoryᵒᵖ).flip.obj
      (Opposite.op ⦋0⦌) ≅ d.R from Iso.refl d.R).symm ≪≫
    @asIso (C ⥤ C) _ _ _ ((rightFactor d).i.app (Opposite.op ⦋0⦌))
      (rightFactor_zero_i_isIso d) ≪≫
        (CategoryTheory.flipCompEvaluation (rightFactor d).Z
          (Opposite.op ⦋0⦌)).symm

/-- The whole cosimplicial degree-zero identification is the original constructed right factor. -/
theorem leftZeroIso_hom (X : C) :
    (leftZeroIso d).hom.app X = ((leftResolution d).app X).app ⦋0⦌ := by
  change (CategoryTheory.flipCompEvaluation (leftFactor d).Z ⦋0⦌ ≪≫
    @asIso (C ⥤ C) _ _ _ ((leftFactor d).p.app ⦋0⦌)
      (leftFactor_zero_p_isIso d) ≪≫ Iso.refl d.Q).hom.app X =
        ((leftFactor d).p.app ⦋0⦌).app X
  simp [CategoryTheory.flipCompEvaluation]

/-- The whole simplicial degree-zero identification is the original constructed left factor. -/
theorem rightZeroIso_hom (X : C) :
    (rightZeroIso d).hom.app X = ((rightResolution d).app X).app (Opposite.op ⦋0⦌) := by
  change ((Iso.refl d.R).symm ≪≫
    @asIso (C ⥤ C) _ _ _ ((rightFactor d).i.app (Opposite.op ⦋0⦌))
      (rightFactor_zero_i_isIso d) ≪≫
        (CategoryTheory.flipCompEvaluation (rightFactor d).Z
          (Opposite.op ⦋0⦌)).symm).hom.app X =
            ((rightFactor d).i.app (Opposite.op ⦋0⦌)).app X
  simp [CategoryTheory.flipCompEvaluation]

/-- The actual cosimplicial augmentation retains the same original Q counit. -/
def augmentation : leftFrame d ⟶ CosimplicialObject.const C :=
  leftResolution d ≫ Functor.whiskerRight d.q (CosimplicialObject.const C) ≫
    (Functor.leftUnitor (CosimplicialObject.const C)).hom

/-- The actual simplicial coaugmentation retains the same original R unit. -/
def coaugmentation : SimplicialObject.const C ⟶ rightFrame d :=
  (Functor.leftUnitor (SimplicialObject.const C)).inv ≫
    Functor.whiskerRight d.r (SimplicialObject.const C) ≫ rightResolution d

/-- Every augmentation degree uses the constructed resolution and unchanged original Q counit. -/
theorem augmentation_app (X : C) (j : SimplexCategory) :
    ((augmentation d).app X).app j = ((leftResolution d).app X).app j ≫ d.q.app X := by
  simp [augmentation]

/-- Every coaugmentation degree uses the unchanged original R unit and constructed resolution. -/
theorem coaugmentation_app (X : C) (j : SimplexCategoryᵒᵖ) :
    ((coaugmentation d).app X).app j = d.r.app X ≫ ((rightResolution d).app X).app j := by
  change 𝟙 X ≫ d.r.app X ≫ ((rightResolution d).app X).app j = _
  exact Category.id_comp _

/-- The same original Q counit follows the actual natural degree-zero identification. -/
theorem augmentation_zero (X : C) :
    ((augmentation d).app X).app ⦋0⦌ = (leftZeroIso d).hom.app X ≫ d.q.app X := by
  rw [augmentation_app, leftZeroIso_hom]

/-- The same original R unit precedes the actual natural degree-zero identification. -/
theorem coaugmentation_zero (X : C) :
    ((coaugmentation d).app X).app (Opposite.op ⦋0⦌) =
      d.r.app X ≫ (rightZeroIso d).hom.app X := by
  rw [coaugmentation_app, rightZeroIso_hom]

/-- The same actual cosimplicial resolution has original trivial-fibration components. -/
theorem leftResolution_trivialFibration (X : C) (j : SimplexCategory) :
    trivialFibrations C (((leftResolution d).app X).app j) := by
  let f := Functor.whiskerRight (leftFactor d).p ((evaluation C C).obj X)
  have hp : ∀ k, trivialFibrations C (ReedyStructure.matchingCorner
      SimplexCategory.reedy f k) := by
    intro k
    exact (ReedyStructure.EvaluationCorners.matching_mem_iff
      SimplexCategory.reedy (leftFactor d).p X k (trivialFibrations C)).mp
        ((leftFactor d).hp k X)
  exact ReedyModel.component_trivialFibration_of_matchingCorners
    SimplexCategory.reedy f hp j

/-- The same actual simplicial resolution has original trivial-cofibration components. -/
theorem rightResolution_trivialCofibration (X : C) (j : SimplexCategoryᵒᵖ) :
    trivialCofibrations C (((rightResolution d).app X).app j) := by
  let f := Functor.whiskerRight (rightFactor d).i ((evaluation C C).obj X)
  have hi : ∀ k, trivialCofibrations C (ReedyStructure.latchingCorner
      SimplexCategory.reedyOp f k) := by
    intro k
    exact (ReedyStructure.EvaluationCorners.latching_mem_iff
      SimplexCategory.reedyOp (rightFactor d).i X k (trivialCofibrations C)).mp
        ((rightFactor d).hi k X)
  exact ReedyModel.component_trivialCofibration_of_latchingCorners
    SimplexCategory.reedyOp f hi j

/-- Every actual cosimplicial resolution map is weak in the same original coefficient model. -/
theorem leftResolution_weak (X : C) (j : SimplexCategory) :
    weakEquivalences C (((leftResolution d).app X).app j) :=
  (leftResolution_trivialFibration d X j).2

/-- Every actual simplicial resolution map is weak in the same original coefficient model. -/
theorem rightResolution_weak (X : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((rightResolution d).app X).app j) :=
  (rightResolution_trivialCofibration d X j).2

/-- The actual original-Q augmentation is weak at every original degree. -/
theorem augmentation_weak (X : C) (j : SimplexCategory) :
    weakEquivalences C (((augmentation d).app X).app j) := by
  rw [augmentation_app]
  exact (weakEquivalences C).comp_mem _ _ (leftResolution_weak d X j)
    (d.q_trivialFibration X).2

/-- The actual original-R coaugmentation is weak at every original degree. -/
theorem coaugmentation_weak (X : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((coaugmentation d).app X).app j) := by
  rw [coaugmentation_app]
  exact (weakEquivalences C).comp_mem _ _
    (d.r_trivialCofibration X).2 (rightResolution_weak d X j)

/-- Every original cosimplicial structure map of the actual left resolution is weak. -/
theorem leftFrame_map_weak (X : C) {i j : SimplexCategory} (g : i ⟶ j) :
    weakEquivalences C (((leftFrame d).obj X).map g) := by
  have hn : ((leftFrame d).obj X).map g ≫ ((leftResolution d).app X).app j =
      ((leftResolution d).app X).app i :=
    (((leftResolution d).app X).naturality g).trans (Category.comp_id _)
  exact (weakEquivalences C).of_postcomp (W' := weakEquivalences C)
    (((leftFrame d).obj X).map g) (((leftResolution d).app X).app j)
    (leftResolution_weak d X j) (hn.symm ▸ leftResolution_weak d X i)

/-- Every original simplicial structure map of the actual right resolution is weak. -/
theorem rightFrame_map_weak (X : C) {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    weakEquivalences C (((rightFrame d).obj X).map g) := by
  have hn : ((rightResolution d).app X).app i ≫ ((rightFrame d).obj X).map g =
      ((rightResolution d).app X).app j :=
    (((rightResolution d).app X).naturality g).symm.trans (Category.id_comp _)
  exact (weakEquivalences C).of_precomp (W' := weakEquivalences C)
    (((rightResolution d).app X).app i) (((rightFrame d).obj X).map g)
    (rightResolution_weak d X i) (hn.symm ▸ rightResolution_weak d X j)

/-- The actual left degree-zero object is cofibrant through the same original Q isomorphism. -/
theorem leftFrame_zero_isCofibrant (X : C) :
    IsCofibrant (((leftFrame d).obj X).obj ⦋0⦌) := by
  let _ := d.q_cofibrant X
  exact isCofibrant_of_cofibration ((leftZeroIso d).app X).inv

/-- The actual right degree-zero object is fibrant through the same original R isomorphism. -/
theorem rightFrame_zero_isFibrant (X : C) :
    IsFibrant (((rightFrame d).obj X).obj (Opposite.op ⦋0⦌)) := by
  let _ := d.r_fibrant X
  exact isFibrant_of_fibration ((rightZeroIso d).app X).inv

/-- The actual least-degree left latching map is a cofibration from its original empty boundary. -/
theorem leftFrame_latching_zero (X : C) :
    cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy
      ((leftFrame d).obj X) ⦋0⦌) := by
  have hI : IsInitial (colimit (SimplexCategory.reedy.latchingDiagram
      ((leftFrame d).obj X) ⦋0⦌)) :=
    isColimitEquivIsInitialOfIsEmpty C (colimit.cocone _) (colimit.isColimit _)
  exact (cofibration_iff _).mp
    ((isCofibrant_iff_of_isInitial _ hI).mp (leftFrame_zero_isCofibrant d X))

/-- The actual least-degree right matching map is a fibration to its original empty boundary. -/
theorem rightFrame_matching_zero (X : C) :
    fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((rightFrame d).obj X) (Opposite.op ⦋0⦌)) := by
  have hT : IsTerminal (limit (SimplexCategory.reedyOp.matchingDiagram
      ((rightFrame d).obj X) (Opposite.op ⦋0⦌))) :=
    isLimitEquivIsTerminalOfIsEmpty C (limit.cone _) (limit.isLimit _)
  exact (fibration_iff _).mp
    ((isFibrant_iff_of_isTerminal _ hT).mp (rightFrame_zero_isFibrant d X))

/-- Every actual positive-degree left latching map is a cofibration from the original I corner. -/
theorem leftFrame_latching_positive (X : C) (j : SimplexCategory) (hj : 0 < j.len) :
    cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy
      ((leftFrame d).obj X) j) := by
  let f := (fromLeftFree d).app X
  have hi : cofibrations C (ReedyStructure.latchingCorner SimplexCategory.reedy f j) :=
    (ReedyStructure.EvaluationCorners.latching_mem_iff
      SimplexCategory.reedy (leftFactor d).i X j (cofibrations C)).mp ((leftFactor d).hi j X)
  let _ : IsIso (ReedyStructure.latchingMap SimplexCategory.reedy
      ((FrameEndpoints.originalLeft d).obj X) j) :=
    FramingEndpoints.leftFreeLatchingMap_isIso (d.Q.obj X) j hj
  let i := pushout.inr
    (ReedyStructure.latchingMap SimplexCategory.reedy ((FrameEndpoints.originalLeft d).obj X) j)
    (colimMap (SimplexCategory.reedy.latchingTransformation f j))
  let _ : IsIso i := by dsimp only [i]; infer_instance
  rw [← ReedyStructure.latchingCorner_inr SimplexCategory.reedy f j]
  exact (cofibrations C).comp_mem _ _ ((cofibrations C).of_isIso i) hi

/-- Every actual positive-degree right matching map is a fibration from the original J corner. -/
theorem rightFrame_matching_positive (X : C) (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len) :
    fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((rightFrame d).obj X) j) := by
  let f := (toRightFree d).app X
  have hp : fibrations C (ReedyStructure.matchingCorner SimplexCategory.reedyOp f j) :=
    (ReedyStructure.EvaluationCorners.matching_mem_iff
      SimplexCategory.reedyOp (rightFactor d).p X j (fibrations C)).mp ((rightFactor d).hp j X)
  let _ : IsIso (ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((FrameEndpoints.originalRight d).obj X) j) :=
    FramingEndpoints.rightFreeMatchingMap_isIso (d.R.obj X) j hj
  let p := pullback.fst
    (limMap (SimplexCategory.reedyOp.matchingTransformation f j))
    (ReedyStructure.matchingMap SimplexCategory.reedyOp ((FrameEndpoints.originalRight d).obj X) j)
  let _ : IsIso p := by dsimp only [p]; infer_instance
  rw [← ReedyStructure.matchingCorner_fst SimplexCategory.reedyOp f j]
  exact (fibrations C).comp_mem _ _ hp ((fibrations C).of_isIso p)

/-- Every original left latching boundary of the actual chosen resolution is a cofibration. -/
theorem leftFrame_latching_cofibration (X : C) (j : SimplexCategory) :
    cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy
      ((leftFrame d).obj X) j) := by
  by_cases hj : j.len = 0
  · have h : j = ⦋0⦌ := SimplexCategory.ext hj
    subst j
    exact leftFrame_latching_zero d X
  · exact leftFrame_latching_positive d X j (Nat.pos_of_ne_zero hj)

/-- Every original right matching boundary of the actual chosen resolution is a fibration. -/
theorem rightFrame_matching_fibration (X : C) (j : SimplexCategoryᵒᵖ) :
    fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((rightFrame d).obj X) j) := by
  by_cases hj : j.unop.len = 0
  · have h : j = Opposite.op ⦋0⦌ := Opposite.unop_injective (SimplexCategory.ext hj)
    subst j
    exact rightFrame_matching_zero d X
  · exact rightFrame_matching_positive d X j (Nat.pos_of_ne_zero hj)


end HomotopicalAlgebra.FunctorialFramings

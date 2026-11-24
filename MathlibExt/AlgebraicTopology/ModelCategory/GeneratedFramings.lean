/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.FramingHomotopy
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFunctorialReplacements
public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.ModelCategory.ReedyGenerated
public import MathlibExt.AlgebraicTopology.SimplexCategory.Reedy
public import MathlibExt.AlgebraicTopology.SimplexCategory.ReedyComparison
public import MathlibExt.CategoryTheory.Reedy.FactorizationCorners
public import MathlibExt.CategoryTheory.Reedy.DegreeZero
public import MathlibExt.CategoryTheory.Reedy.Corner

/-!
# Actual functorial resolution diagrams from the original generated Q and R

The original finite endpoint fold and diagonal are factored in `C ⥤ C`, using exactly the
original coefficient factories. Parameter naturality is internal to that category. The
actual original boundary shapes suffice for the degree construction, so an ordinary
model category's finite limits and colimits are retained without stronger completeness.

The least-degree identity normalization keeps the same original Q and R endpoints by
natural isomorphisms. Both original replacement arrows remain in the augmentation and
coaugmentation. The framing class and weak-constancy proofs use these actual diagrams.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty Simplicial

namespace HomotopicalAlgebra.GeneratedFramings

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The unchanged original generated-Q fold, with its parameter and degree variables flipped. -/
def leftEndpointArrow : (FramingEndpoints.originalLeft d).flip ⟶
    (Q d ⋙ CosimplicialObject.const C).flip :=
  FunctorialFramings.leftEndpointArrow (GeneratedFunctorialReplacements.fromGeneration d)

/-- The unchanged original generated-R diagonal, with its parameter and degree variables flipped. -/
def rightEndpointArrow : (R d ⋙ SimplicialObject.const C).flip ⟶
    (FramingEndpoints.originalRight d).flip :=
  FunctorialFramings.rightEndpointArrow (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual complete original I degree factorization of the generated-Q fold. -/
def leftFactor :
    MapFactorizationData
      (CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedy
        ((cofibrations C).functorCategory C))
      (CategoryTheory.ReedyStructure.matchingClass SimplexCategory.reedy
        ((trivialFibrations C).functorCategory C)) (leftEndpointArrow d) :=
  FunctorialFramings.leftFactor (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual complete original J degree factorization of the generated-R diagonal. -/
def rightFactor :
    MapFactorizationData
      (CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp
        ((trivialCofibrations C).functorCategory C))
      (CategoryTheory.ReedyStructure.matchingClass SimplexCategory.reedyOp
        ((fibrations C).functorCategory C)) (rightEndpointArrow d) :=
  FunctorialFramings.rightFactor (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual original I-factor middle diagrams as a functor of every original object and map. -/
def leftFrame : C ⥤ CosimplicialObject C :=
  FunctorialFramings.leftFrame (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual original J-factor middle diagrams as a functor of every original object and map. -/
def rightFrame : C ⥤ SimplicialObject C :=
  FunctorialFramings.rightFrame (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual whole original I source factor into the cosimplicial middle diagram. -/
def fromLeftFree : FramingEndpoints.originalLeft d ⟶ leftFrame d :=
  FunctorialFramings.fromLeftFree (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual whole original I target factor to the same original generated Q. -/
def leftResolution : leftFrame d ⟶ Q d ⋙ CosimplicialObject.const C :=
  FunctorialFramings.leftResolution (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual whole original J source factor from the same original generated R. -/
def rightResolution : R d ⋙ SimplicialObject.const C ⟶ rightFrame d :=
  FunctorialFramings.rightResolution (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual whole original J target factor to the original finite-power endpoint. -/
def toRightFree : rightFrame d ⟶ FramingEndpoints.originalRight d :=
  FunctorialFramings.toRightFree (GeneratedFunctorialReplacements.fromGeneration d)

/-- Both actual I factors recover the unchanged original generated-Q fold. -/
theorem left_fac : fromLeftFree d ≫ leftResolution d =
    FramingEndpoints.originalCosimplicialFold d :=
  FunctorialFramings.left_fac (GeneratedFunctorialReplacements.fromGeneration d)

/-- Both actual J factors recover the unchanged original generated-R diagonal. -/
theorem right_fac : rightResolution d ≫ toRightFree d =
    FramingEndpoints.originalSimplicialDiagonal d :=
  FunctorialFramings.right_fac (GeneratedFunctorialReplacements.fromGeneration d)

/-- The original generated-Q endpoint coefficient is a whole natural isomorphism in degree zero. -/
instance leftEndpointArrow_zero_isIso : IsIso ((leftEndpointArrow d).app ⦋0⦌) :=
  FunctorialFramings.leftEndpointArrow_zero_isIso (GeneratedFunctorialReplacements.fromGeneration d)

/-- The original generated-R endpoint coefficient is a whole natural isomorphism in degree zero. -/
instance rightEndpointArrow_zero_isIso :
    IsIso ((rightEndpointArrow d).app (Opposite.op ⦋0⦌)) :=
  FunctorialFramings.rightEndpointArrow_zero_isIso
    (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual global I right factor keeps the original Q endpoint in degree zero. -/
instance leftFactor_zero_p_isIso : IsIso ((leftFactor d).p.app ⦋0⦌) :=
  FunctorialFramings.leftFactor_zero_p_isIso (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual global J left factor keeps the original R endpoint in degree zero. -/
instance rightFactor_zero_i_isIso : IsIso ((rightFactor d).i.app (Opposite.op ⦋0⦌)) :=
  FunctorialFramings.rightFactor_zero_i_isIso (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual cosimplicial degree-zero middle is naturally the same original generated Q. -/
def leftZeroIso : leftFrame d ⋙ (evaluation SimplexCategory C).obj ⦋0⦌ ≅ Q d :=
  FunctorialFramings.leftZeroIso (GeneratedFunctorialReplacements.fromGeneration d)

/-- The same original generated R naturally identifies the actual simplicial degree-zero middle. -/
def rightZeroIso : R d ≅ rightFrame d ⋙
    (evaluation SimplexCategoryᵒᵖ C).obj (Opposite.op ⦋0⦌) :=
  FunctorialFramings.rightZeroIso (GeneratedFunctorialReplacements.fromGeneration d)

/-- The whole cosimplicial degree-zero identification is the original constructed right factor. -/
theorem leftZeroIso_hom (X : C) :
    (leftZeroIso d).hom.app X = ((leftResolution d).app X).app ⦋0⦌ :=
  FunctorialFramings.leftZeroIso_hom (GeneratedFunctorialReplacements.fromGeneration d) X

/-- The whole simplicial degree-zero identification is the original constructed left factor. -/
theorem rightZeroIso_hom (X : C) :
    (rightZeroIso d).hom.app X = ((rightResolution d).app X).app (Opposite.op ⦋0⦌) :=
  FunctorialFramings.rightZeroIso_hom (GeneratedFunctorialReplacements.fromGeneration d) X

/-- The actual cosimplicial augmentation retains the same original Q counit. -/
def augmentation : leftFrame d ⟶ CosimplicialObject.const C :=
  FunctorialFramings.augmentation (GeneratedFunctorialReplacements.fromGeneration d)

/-- The actual simplicial coaugmentation retains the same original R unit. -/
def coaugmentation : SimplicialObject.const C ⟶ rightFrame d :=
  FunctorialFramings.coaugmentation (GeneratedFunctorialReplacements.fromGeneration d)

/-- Every augmentation degree uses the constructed resolution and unchanged original Q counit. -/
theorem augmentation_app (X : C) (j : SimplexCategory) :
    ((augmentation d).app X).app j = ((leftResolution d).app X).app j ≫ (counit d).app X :=
  FunctorialFramings.augmentation_app (GeneratedFunctorialReplacements.fromGeneration d) X j

/-- Every coaugmentation degree uses the unchanged original R unit and constructed resolution. -/
theorem coaugmentation_app (X : C) (j : SimplexCategoryᵒᵖ) :
    ((coaugmentation d).app X).app j = (unit d).app X ≫ ((rightResolution d).app X).app j :=
  FunctorialFramings.coaugmentation_app (GeneratedFunctorialReplacements.fromGeneration d) X j

/-- The same original Q counit follows the actual natural degree-zero identification. -/
theorem augmentation_zero (X : C) :
    ((augmentation d).app X).app ⦋0⦌ = (leftZeroIso d).hom.app X ≫ (counit d).app X :=
  FunctorialFramings.augmentation_zero (GeneratedFunctorialReplacements.fromGeneration d) X

/-- The same original R unit precedes the actual natural degree-zero identification. -/
theorem coaugmentation_zero (X : C) :
    ((coaugmentation d).app X).app (Opposite.op ⦋0⦌) =
      (unit d).app X ≫ (rightZeroIso d).hom.app X :=
  FunctorialFramings.coaugmentation_zero (GeneratedFunctorialReplacements.fromGeneration d) X

/-- The same actual cosimplicial resolution has original trivial-fibration components. -/
theorem leftResolution_trivialFibration (X : C) (j : SimplexCategory) :
    trivialFibrations C (((leftResolution d).app X).app j) :=
  FunctorialFramings.leftResolution_trivialFibration (GeneratedFunctorialReplacements.fromGeneration
    d) X j

/-- The same actual simplicial resolution has original trivial-cofibration components. -/
theorem rightResolution_trivialCofibration (X : C) (j : SimplexCategoryᵒᵖ) :
    trivialCofibrations C (((rightResolution d).app X).app j) :=
  FunctorialFramings.rightResolution_trivialCofibration
    (GeneratedFunctorialReplacements.fromGeneration d) X j

/-- Every actual cosimplicial resolution map is weak in the same original coefficient model. -/
theorem leftResolution_weak (X : C) (j : SimplexCategory) :
    weakEquivalences C (((leftResolution d).app X).app j) :=
  FunctorialFramings.leftResolution_weak (GeneratedFunctorialReplacements.fromGeneration d) X j

/-- Every actual simplicial resolution map is weak in the same original coefficient model. -/
theorem rightResolution_weak (X : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((rightResolution d).app X).app j) :=
  FunctorialFramings.rightResolution_weak (GeneratedFunctorialReplacements.fromGeneration d) X j

/-- The actual original-Q augmentation is weak at every original degree. -/
theorem augmentation_weak (X : C) (j : SimplexCategory) :
    weakEquivalences C (((augmentation d).app X).app j) :=
  FunctorialFramings.augmentation_weak (GeneratedFunctorialReplacements.fromGeneration d) X j

/-- The actual original-R coaugmentation is weak at every original degree. -/
theorem coaugmentation_weak (X : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((coaugmentation d).app X).app j) :=
  FunctorialFramings.coaugmentation_weak (GeneratedFunctorialReplacements.fromGeneration d) X j

/-- Every original cosimplicial structure map of the actual left resolution is weak. -/
theorem leftFrame_map_weak (X : C) {i j : SimplexCategory} (g : i ⟶ j) :
    weakEquivalences C (((leftFrame d).obj X).map g) :=
  FunctorialFramings.leftFrame_map_weak (GeneratedFunctorialReplacements.fromGeneration d) X g

/-- Every original simplicial structure map of the actual right resolution is weak. -/
theorem rightFrame_map_weak (X : C) {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    weakEquivalences C (((rightFrame d).obj X).map g) :=
  FunctorialFramings.rightFrame_map_weak (GeneratedFunctorialReplacements.fromGeneration d) X g

/-- The actual left degree-zero object is cofibrant through the same original Q isomorphism. -/
theorem leftFrame_zero_isCofibrant (X : C) :
    IsCofibrant (((leftFrame d).obj X).obj ⦋0⦌) :=
  FunctorialFramings.leftFrame_zero_isCofibrant (GeneratedFunctorialReplacements.fromGeneration d) X

/-- The actual right degree-zero object is fibrant through the same original R isomorphism. -/
theorem rightFrame_zero_isFibrant (X : C) :
    IsFibrant (((rightFrame d).obj X).obj (Opposite.op ⦋0⦌)) :=
  FunctorialFramings.rightFrame_zero_isFibrant (GeneratedFunctorialReplacements.fromGeneration d) X

/-- The actual least-degree left latching map is a cofibration from its original empty boundary. -/
theorem leftFrame_latching_zero (X : C) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy
      ((leftFrame d).obj X) ⦋0⦌) :=
  FunctorialFramings.leftFrame_latching_zero (GeneratedFunctorialReplacements.fromGeneration d) X

/-- The actual least-degree right matching map is a fibration to its original empty boundary. -/
theorem rightFrame_matching_zero (X : C) :
    fibrations C (CategoryTheory.ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((rightFrame d).obj X) (Opposite.op ⦋0⦌)) :=
  FunctorialFramings.rightFrame_matching_zero (GeneratedFunctorialReplacements.fromGeneration d) X

/-- Every actual positive-degree left latching map is a cofibration from the original I corner. -/
theorem leftFrame_latching_positive (X : C) (j : SimplexCategory) (hj : 0 < j.len) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy
      ((leftFrame d).obj X) j) :=
  FunctorialFramings.leftFrame_latching_positive (GeneratedFunctorialReplacements.fromGeneration d)
    X j hj

/-- Every actual positive-degree right matching map is a fibration from the original J corner. -/
theorem rightFrame_matching_positive (X : C) (j : SimplexCategoryᵒᵖ) (hj : 0 < j.unop.len) :
    fibrations C (CategoryTheory.ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((rightFrame d).obj X) j) :=
  FunctorialFramings.rightFrame_matching_positive (GeneratedFunctorialReplacements.fromGeneration d)
    X j hj

/-- Every original left latching boundary of the actual generated resolution is a cofibration. -/
theorem leftFrame_latching_cofibration (X : C) (j : SimplexCategory) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy
      ((leftFrame d).obj X) j) :=
  FunctorialFramings.leftFrame_latching_cofibration (GeneratedFunctorialReplacements.fromGeneration
    d) X j

/-- Every original right matching boundary of the actual generated resolution is a fibration. -/
theorem rightFrame_matching_fibration (X : C) (j : SimplexCategoryᵒᵖ) :
    fibrations C (CategoryTheory.ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((rightFrame d).obj X) j) :=
  FunctorialFramings.rightFrame_matching_fibration (GeneratedFunctorialReplacements.fromGeneration
    d) X j


/-- The generated endpoint fold is the exact original fixed-generation fold. -/
theorem leftEndpointArrow_original : leftEndpointArrow d =
    (flipFunctor C SimplexCategory C).map (FramingEndpoints.originalCosimplicialFold d) := rfl

/-- The generated endpoint diagonal is the exact original fixed-generation diagonal. -/
theorem rightEndpointArrow_original : rightEndpointArrow d =
    (flipFunctor C SimplexCategoryᵒᵖ C).map (FramingEndpoints.originalSimplicialDiagonal d) := rfl

/-- The shared core retains the literal original I coefficient factory and degree factorization. -/
theorem leftFactor_original : leftFactor d =
    ReedyStructure.DegreeFactorization.classifiedFactor SimplexCategory.reedy
      (leftEndpointArrow d) (fun {_ _} f ↦ FramingCoefficientFactory.generatedCofibrant d f) := rfl

/-- The shared core retains the literal original J coefficient factory and degree factorization. -/
theorem rightFactor_original : rightFactor d =
    ReedyStructure.DegreeFactorization.classifiedFactor SimplexCategory.reedyOp
      (rightEndpointArrow d) (fun {_ _} f ↦ FramingCoefficientFactory.generatedFibrant d f) := rfl

/-- The old public generated frame specializes the single core at the original complete generation
data. -/
theorem leftFrame_core : leftFrame d =
    FunctorialFramings.leftFrame (GeneratedFunctorialReplacements.fromGeneration d) := rfl

/-- The old public generated right frame specializes the same core at the original generation data.
-/
theorem rightFrame_core : rightFrame d =
    FunctorialFramings.rightFrame (GeneratedFunctorialReplacements.fromGeneration d) := rfl

/-- The generated augmentation is the same shared-core map on the original generation data. -/
theorem augmentation_core : augmentation d =
    FunctorialFramings.augmentation (GeneratedFunctorialReplacements.fromGeneration d) := rfl

/-- The generated coaugmentation is the same shared-core map on the original generation data. -/
theorem coaugmentation_core : coaugmentation d =
    FunctorialFramings.coaugmentation (GeneratedFunctorialReplacements.fromGeneration d) := rfl

/-- The generated augmentation retains the same original Q counit after the actual degree factor. -/
theorem augmentation_original : augmentation d =
    leftResolution d ≫ Functor.whiskerRight (counit d) (CosimplicialObject.const C) ≫
      (Functor.leftUnitor (CosimplicialObject.const C)).hom := rfl

/-- The generated coaugmentation retains the same original R unit before the actual degree factor.
-/
theorem coaugmentation_original : coaugmentation d =
    (Functor.leftUnitor (SimplicialObject.const C)).inv ≫
      Functor.whiskerRight (unit d) (SimplicialObject.const C) ≫ rightResolution d := rfl

end HomotopicalAlgebra.GeneratedFramings

end
end
end

section



/-!
# Actual bifibrant simplicial resolution of the original generated Q

The original R unit on a genuinely cofibrant Q object makes RQ cofibrant. The actual
constant simplicial latching boundaries are isomorphisms in positive degrees. The
original J-framing factor therefore gives a Reedy cofibrant and Reedy fibrant,
homotopically constant simplicial resolution, retaining every original Q and R map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty Simplicial

namespace HomotopicalAlgebra.GeneratedFramings

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The original R unit on the original cofibrant Q object makes the unchanged RQ cofibrant. -/
theorem RQ_isCofibrant (X : C) : IsCofibrant ((R d).obj ((Q d).obj X)) := by
  let _ : IsCofibrant ((𝟭 C).obj ((Q d).obj X)) :=
    GeneratedFunctorialReplacements.Q_isCofibrant d X
  let _ : Cofibration ((unit d).app ((Q d).obj X)) :=
    (cofibration_iff _).mpr (GeneratedFunctorialReplacements.unit_trivialCofibration d ((Q d).obj
      X)).1
  exact isCofibrant_of_cofibration ((unit d).app ((Q d).obj X))

/-- The actual right-frame degree-zero value at Q retains the original cofibrant RQ endpoint. -/
theorem rightFrame_Q_zero_isCofibrant (X : C) :
    IsCofibrant (((rightFrame d).obj ((Q d).obj X)).obj (Opposite.op ⦋0⦌)) := by
  let _ := RQ_isCofibrant d X
  exact isCofibrant_of_cofibration ((rightZeroIso d).app ((Q d).obj X)).hom

/-- The actual right-frame least-degree latching map at Q has the original cofibrant endpoint. -/
theorem rightFrame_Q_latching_zero (X : C) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      ((rightFrame d).obj ((Q d).obj X)) (Opposite.op ⦋0⦌)) := by
  have hI : IsInitial (colimit (SimplexCategory.reedyOp.latchingDiagram
      ((rightFrame d).obj ((Q d).obj X)) (Opposite.op ⦋0⦌))) :=
    isColimitEquivIsInitialOfIsEmpty C (colimit.cocone _) (colimit.isColimit _)
  exact (cofibration_iff _).mp
    ((isCofibrant_iff_of_isInitial _ hI).mp (rightFrame_Q_zero_isCofibrant d X))

/-- Every original positive right-frame latching map at Q is a cofibration from its actual J corner.
-/
theorem rightFrame_Q_latching_positive (X : C) (j : SimplexCategoryᵒᵖ)
    (hj : 0 < j.unop.len) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      ((rightFrame d).obj ((Q d).obj X)) j) := by
  let Y := (Q d).obj X
  let f := (rightResolution d).app Y
  have hi : cofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp f
    j) :=
    ((CategoryTheory.ReedyStructure.EvaluationCorners.latching_mem_iff
      SimplexCategory.reedyOp (rightFactor d).i Y j (trivialCofibrations C)).mp
        ((rightFactor d).hi j Y)).1
  let _ : IsIso (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      ((SimplicialObject.const C).obj ((R d).obj Y)) j) :=
    FramingEndpoints.constantSimplicialLatchingMap_isIso ((R d).obj Y) j hj
  let i := pushout.inr
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      ((SimplicialObject.const C).obj ((R d).obj Y)) j)
    (colimMap (SimplexCategory.reedyOp.latchingTransformation f j))
  let _ : IsIso i := by dsimp only [i]; infer_instance
  rw [← CategoryTheory.ReedyStructure.latchingCorner_inr SimplexCategory.reedyOp f j]
  exact (cofibrations C).comp_mem _ _ ((cofibrations C).of_isIso i) hi

/-- All actual original right-frame latching maps at Q are cofibrations. -/
theorem rightFrame_Q_latching_cofibration (X : C) (j : SimplexCategoryᵒᵖ) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      ((rightFrame d).obj ((Q d).obj X)) j) := by
  by_cases hj : j.unop.len = 0
  · have h : j = Opposite.op ⦋0⦌ := Opposite.unop_injective (SimplexCategory.ext hj)
    subst j
    exact rightFrame_Q_latching_zero d X
  · exact rightFrame_Q_latching_positive d X j (Nat.pos_of_ne_zero hj)

/-- The actual functorial simplicial bifibrant resolution uses the same original generated Q. -/
def bifibrantFrame : C ⥤ SimplicialObject C := Q d ⋙ rightFrame d

/-- Every original Q object is retained as the input to the same actual right frame. -/
theorem bifibrantFrame_obj (X : C) :
    (bifibrantFrame d).obj X = (rightFrame d).obj ((Q d).obj X) := rfl

/-- Every original Q morphism is retained by the entire actual bifibrant frame functor. -/
theorem bifibrantFrame_map {X Y : C} (f : X ⟶ Y) :
    (bifibrantFrame d).map f = (rightFrame d).map ((Q d).map f) := rfl

/-- The actual natural comparison from constant Q keeps the original R unit and J framing maps. -/
def bifibrantFromQ : Q d ⋙ SimplicialObject.const C ⟶ bifibrantFrame d :=
  Functor.whiskerLeft (Q d) (coaugmentation d)

/-- Every original comparison component is the unchanged R unit followed by the actual J frame. -/
theorem bifibrantFromQ_app (X : C) (j : SimplexCategoryᵒᵖ) :
    ((bifibrantFromQ d).app X).app j =
      (unit d).app ((Q d).obj X) ≫ ((rightResolution d).app ((Q d).obj X)).app j :=
  coaugmentation_app d ((Q d).obj X) j

/-- The actual constant-Q comparison is weak in every original degree. -/
theorem bifibrantFromQ_weak (X : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((bifibrantFromQ d).app X).app j) :=
  coaugmentation_weak d ((Q d).obj X) j

/-- Every original bifibrant-frame latching map is a cofibration. -/
theorem bifibrantFrame_latching_cofibration (X : C) (j : SimplexCategoryᵒᵖ) :
    cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedyOp
      ((bifibrantFrame d).obj X) j) := rightFrame_Q_latching_cofibration d X j

/-- Every original bifibrant-frame matching map is a fibration. -/
theorem bifibrantFrame_matching_fibration (X : C) (j : SimplexCategoryᵒᵖ) :
    fibrations C (CategoryTheory.ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((bifibrantFrame d).obj X) j) := rightFrame_matching_fibration d ((Q d).obj X) j

/-- Every actual bifibrant-frame structure map remains weak in the original model. -/
theorem bifibrantFrame_map_weak (X : C) {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    weakEquivalences C (((bifibrantFrame d).obj X).map g) :=
  rightFrame_map_weak d ((Q d).obj X) g

end HomotopicalAlgebra.GeneratedFramings

end
end
end

section



/-!
# The actual finite-boundary Reedy models for the original generated frames

The original source generation data supplies both complete Reedy factories on
the original cosimplicial and simplicial diagram categories. Their actual
latching and matching shapes are finite, so the model category's finite limits
and colimits suffice. Every model class and each original factory is retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra.GeneratedFramingModels

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The genuine cosimplicial Reedy model uses the same original generated coefficient factories. -/
@[instance_reducible]
def cosimplicialModel : ModelCategory (CosimplicialObject C) :=
  ReedyModel.generatedModelCategory SimplexCategory.reedy d

/-- The actual canonical simplicial model and the complete originally supplied factor factories. -/
structure SimplicialConstruction where
  /-- The established canonical simplicial Reedy model. -/
  model : ModelCategory (SimplicialObject C)
  /-- The complete original cofibration factory in the selected model's actual classes. -/
  cofibrantFactory :
    letI := model
    FunctorialFactorizationData (cofibrations (SimplicialObject C))
      (trivialFibrations (SimplicialObject C))
  /-- The complete original fibration factory in the selected model's actual classes. -/
  fibrantFactory :
    letI := model
    FunctorialFactorizationData (trivialCofibrations (SimplicialObject C))
      (fibrations (SimplicialObject C))

/-- Select the established model and retain both original generated factories with all their maps.
-/
def simplicialConstruction : SimplicialConstruction (C := C) where
  model := SimplicialObject.reedyModelCategory
  cofibrantFactory := SimplexCategory.ReedyCanonicalComparison.canonicalCofibrantFactorizationData
    d.cofibrantFactorizationData d.fibrantFactorizationData
  fibrantFactory := SimplexCategory.ReedyCanonicalComparison.canonicalFibrantFactorizationData
    d.cofibrantFactorizationData d.fibrantFactorizationData

/-- The canonical simplicial Reedy model selected together with the original generated factories. -/
@[instance_reducible]
def simplicialModel : ModelCategory (SimplicialObject C) := (simplicialConstruction d).model

/-- The selected full simplicial model dictionary is the established canonical dictionary. -/
theorem simplicialModel_eq_canonical :
    simplicialModel d = SimplicialObject.reedyModelCategory (C := C) := rfl

/-- The selected canonical dictionary agrees with the original generated dictionary. -/
theorem simplicialModel_eq_generated :
    simplicialModel d = ReedyModel.generatedModelCategory SimplexCategory.reedyOp d :=
  (SimplexCategory.ReedyCanonicalComparison.modelCategory_eq_canonical
    d.cofibrantFactorizationData d.fibrantFactorizationData).symm

/-- The actual cosimplicial weak maps are the original objectwise source weak maps. -/
theorem cosimplicial_weakEquivalences_eq :
    letI := cosimplicialModel d
    weakEquivalences (CosimplicialObject C) = (weakEquivalences C).functorCategory
      SimplexCategory :=
  ReedyModel.weakEquivalences_eq SimplexCategory.reedy
    d.cofibrantFactorizationData d.fibrantFactorizationData

/-- The actual cosimplicial cofibrations are the original latching-corner source cofibrations. -/
theorem cosimplicial_cofibrations_eq :
    letI := cosimplicialModel d
    cofibrations (CosimplicialObject C) =
      CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedy (cofibrations C) :=
  ReedyModel.cofibrations_eq SimplexCategory.reedy
    d.cofibrantFactorizationData d.fibrantFactorizationData

/-- The actual cosimplicial fibrations are the original matching-corner source fibrations. -/
theorem cosimplicial_fibrations_eq :
    letI := cosimplicialModel d
    fibrations (CosimplicialObject C) =
      CategoryTheory.ReedyStructure.matchingClass SimplexCategory.reedy (fibrations C) :=
  ReedyModel.fibrations_eq SimplexCategory.reedy
    d.cofibrantFactorizationData d.fibrantFactorizationData

/-- The actual cosimplicial trivial cofibrations retain all original source trivial latching
corners. -/
theorem cosimplicial_trivialCofibrations_eq :
    letI := cosimplicialModel d
    trivialCofibrations (CosimplicialObject C) =
      CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedy (trivialCofibrations C) :=
  ReedyModel.trivialCofibrations_eq SimplexCategory.reedy
    d.cofibrantFactorizationData d.fibrantFactorizationData

/-- The actual cosimplicial trivial fibrations retain all original source trivial matching corners.
-/
theorem cosimplicial_trivialFibrations_eq :
    letI := cosimplicialModel d
    trivialFibrations (CosimplicialObject C) =
      CategoryTheory.ReedyStructure.matchingClass SimplexCategory.reedy (trivialFibrations C) :=
  ReedyModel.trivialFibrations_eq SimplexCategory.reedy
    d.cofibrantFactorizationData d.fibrantFactorizationData

/-- The actual simplicial weak maps are the original objectwise source weak maps. -/
theorem simplicial_weakEquivalences_eq :
    letI := simplicialModel d
    weakEquivalences (SimplicialObject C) = (weakEquivalences C).functorCategory
      SimplexCategoryᵒᵖ :=
  SimplexCategory.ReedyCanonicalComparison.canonical_weakEquivalences_eq (C := C)

/-- The actual simplicial cofibrations are the original latching-corner source cofibrations. -/
theorem simplicial_cofibrations_eq :
    letI := simplicialModel d
    cofibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp (cofibrations C) :=
  SimplexCategory.ReedyCanonicalComparison.canonical_cofibrations_eq (C := C)

/-- The actual simplicial fibrations are the original matching-corner source fibrations. -/
theorem simplicial_fibrations_eq :
    letI := simplicialModel d
    fibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.matchingClass SimplexCategory.reedyOp (fibrations C) :=
  SimplexCategory.ReedyCanonicalComparison.canonical_fibrations_eq (C := C)

/-- The actual simplicial trivial cofibrations retain all original source trivial latching corners.
-/
theorem simplicial_trivialCofibrations_eq :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp (trivialCofibrations C) :=
  SimplexCategory.ReedyCanonicalComparison.canonical_trivialCofibrations_eq (C := C)

/-- The actual simplicial trivial fibrations retain all original source trivial matching corners. -/
theorem simplicial_trivialFibrations_eq :
    letI := simplicialModel d
    trivialFibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.matchingClass SimplexCategory.reedyOp (trivialFibrations C) :=
  SimplexCategory.ReedyCanonicalComparison.canonical_trivialFibrations_eq (C := C)

/-- The complete cosimplicial cofibration factory uses the original generated coefficient factory.
-/
def cosimplicialCofibrantFactorizationData :
    letI := cosimplicialModel d
    FunctorialFactorizationData (cofibrations (CosimplicialObject C))
      (trivialFibrations (CosimplicialObject C)) :=
  ReedyModel.generatedCofibrantFactorizationData SimplexCategory.reedy d

/-- The complete cosimplicial fibration factory uses the original generated coefficient factory. -/
def cosimplicialFibrantFactorizationData :
    letI := cosimplicialModel d
    FunctorialFactorizationData (trivialCofibrations (CosimplicialObject C))
      (fibrations (CosimplicialObject C)) :=
  ReedyModel.generatedFibrantFactorizationData SimplexCategory.reedy d

/-- The complete simplicial cofibration factory uses the original generated coefficient factory. -/
def simplicialCofibrantFactorizationData :
    letI := simplicialModel d
    FunctorialFactorizationData (cofibrations (SimplicialObject C))
      (trivialFibrations (SimplicialObject C)) :=
  (simplicialConstruction d).cofibrantFactory

/-- The complete simplicial fibration factory uses the original generated coefficient factory. -/
def simplicialFibrantFactorizationData :
    letI := simplicialModel d
    FunctorialFactorizationData (trivialCofibrations (SimplicialObject C))
      (fibrations (SimplicialObject C)) :=
  (simplicialConstruction d).fibrantFactory

end HomotopicalAlgebra.GeneratedFramingModels

end
end
end

section



/-!
# Actual model membership of original generated frame objects and maps

The original boundary classes recognize the actual Reedy model objects.
Constant source cofibrations retain the original zero-degree coefficient map
and positive isomorphism corners. The original J factory supplies the actual
right-resolution corner class, so both comparison maps are genuine trivial
cofibrations. Model and frame replacement choices have independent cardinals.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wF uC vC

open CategoryTheory Limits MorphismProperty Simplicial
open HomotopicalAlgebra.GeneratedFunctorialReplacements

namespace HomotopicalAlgebra.GeneratedFramingModels

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
  (d : CofibrantGenerationData C κM)

/-- Actual generated simplicial-model cofibrancy uses every original whole latching map. -/
theorem simplicial_isCofibrant_iff (A : SimplicialObject C) :
    letI := simplicialModel d
    IsCofibrant A ↔ ∀ j, Cofibration (CategoryTheory.ReedyStructure.latchingMap
      SimplexCategory.reedyOp A j) := by
  rw [simplicialModel_eq_generated d]
  exact ReedyModel.Shape.isCofibrant_iff_latching SimplexCategory.reedyOp
    d.cofibrantFactorizationData d.fibrantFactorizationData A

/-- Actual generated simplicial-model fibrancy uses every original whole matching map. -/
theorem simplicial_isFibrant_iff (A : SimplicialObject C) :
    letI := simplicialModel d
    IsFibrant A ↔ ∀ j, Fibration (CategoryTheory.ReedyStructure.matchingMap SimplexCategory.reedyOp
      A j) := by
  rw [simplicialModel_eq_generated d]
  exact ReedyModel.Shape.isFibrant_iff_matching SimplexCategory.reedyOp
    d.cofibrantFactorizationData d.fibrantFactorizationData A

/-- Actual generated cosimplicial-model cofibrancy uses the original whole latching maps. -/
theorem cosimplicial_isCofibrant_iff (A : CosimplicialObject C) :
    letI := cosimplicialModel d
    IsCofibrant A ↔ ∀ j, Cofibration (CategoryTheory.ReedyStructure.latchingMap
      SimplexCategory.reedy A j) :=
  ReedyModel.Shape.isCofibrant_iff_latching SimplexCategory.reedy
    d.cofibrantFactorizationData d.fibrantFactorizationData A

/-- The actual constant map of every original source cofibration is a Reedy-model cofibration. -/
theorem constant_cofibration {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    letI := simplicialModel d
    Cofibration ((SimplicialObject.const C).map f) := by
  let _ := simplicialModel d
  rw [simplicialModel_eq_generated d]
  apply (ReedyModel.cofibration_iff_source SimplexCategory.reedyOp
    d.cofibrantFactorizationData d.fibrantFactorizationData _).mpr
  intro j
  exact (cofibration_iff _).mpr (FramingEndpoints.constantSimplicialCorner_mem (cofibrations C) f
    hf j)

/-- The actual constant map of every source trivial cofibration is a Reedy-model trivial
cofibration. -/
theorem constant_trivialCofibration {X Y : C} (f : X ⟶ Y) (hf : trivialCofibrations C f) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((SimplicialObject.const C).map f) := by
  let _ := simplicialModel d
  rw [simplicial_trivialCofibrations_eq d]
  exact FramingEndpoints.constantSimplicial_latchingClass (trivialCofibrations C) f hf

/-- The original constant simplicial object of any source cofibrant object is genuinely Reedy
cofibrant. -/
theorem constant_isCofibrant (X : C) (hX : IsCofibrant X) :
    letI := simplicialModel d
    IsCofibrant ((SimplicialObject.const C).obj X) := by
  let _ := simplicialModel d
  apply (isCofibrant_iff_of_isInitial ((SimplicialObject.const C).map (initial.to X))
    (Functor.isInitialConst SimplexCategoryᵒᵖ initialIsInitial)).mpr
  exact constant_cofibration d (initial.to X) ((cofibration_iff _).mp hX)

section FrameChoices

variable {κF : Cardinal.{wF}} [Fact κF.IsRegular] [OrderBot κF.ord.ToType]
  (e : CofibrantGenerationData C κF)

/-- The same original right frame is genuinely fibrant in the actual model, for independent choices.
-/
theorem rightFrame_isFibrant (Y : C) :
    letI := simplicialModel d
    IsFibrant ((GeneratedFramings.rightFrame e).obj Y) := by
  apply (simplicial_isFibrant_iff d _).mpr
  intro j
  exact (fibration_iff _).mpr (GeneratedFramings.rightFrame_matching_fibration e Y j)

/-- The original bifibrant frame is genuinely cofibrant in the actual model, for independent
choices. -/
theorem bifibrantFrame_isCofibrant (X : C) :
    letI := simplicialModel d
    IsCofibrant ((GeneratedFramings.bifibrantFrame e).obj X) := by
  apply (simplicial_isCofibrant_iff d _).mpr
  intro j
  exact (cofibration_iff _).mpr (GeneratedFramings.bifibrantFrame_latching_cofibration e X j)

/-- The original bifibrant frame is genuinely fibrant in the actual model, for independent choices.
-/
theorem bifibrantFrame_isFibrant (X : C) :
    letI := simplicialModel d
    IsFibrant ((GeneratedFramings.bifibrantFrame e).obj X) := rightFrame_isFibrant d e ((Q e).obj X)

/-- The same original generated Q object remains genuinely cofibrant as a constant simplicial
object. -/
theorem constant_Q_isCofibrant (X : C) :
    letI := simplicialModel d
    IsCofibrant ((SimplicialObject.const C).obj ((Q e).obj X)) :=
  constant_isCofibrant d ((Q e).obj X) (GeneratedFunctorialReplacements.Q_isCofibrant e X)

/-- The original left frame is genuinely cofibrant in the actual cosimplicial model. -/
theorem leftFrame_isCofibrant (X : C) :
    letI := cosimplicialModel d
    IsCofibrant ((GeneratedFramings.leftFrame e).obj X) := by
  apply (cosimplicial_isCofibrant_iff d _).mpr
  intro j
  exact (cofibration_iff _).mpr (GeneratedFramings.leftFrame_latching_cofibration e X j)

/-- The original constant R unit is a true actual Reedy-model trivial cofibration. -/
theorem constant_unit_trivialCofibration (Y : C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((SimplicialObject.const C).map ((unit e).app Y)) :=
  constant_trivialCofibration d ((unit e).app Y)
    (GeneratedFunctorialReplacements.unit_trivialCofibration e Y)

/-- The original J factory proves the actual whole right-resolution model membership. -/
theorem rightResolution_model_trivialCofibration (Y : C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((GeneratedFramings.rightResolution e).app Y) := by
  let _ := simplicialModel d
  rw [simplicial_trivialCofibrations_eq d]
  change ∀ j, trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner
    SimplexCategory.reedyOp ((GeneratedFramings.rightResolution e).app Y) j)
  intro j
  exact (CategoryTheory.ReedyStructure.EvaluationCorners.latching_mem_iff
    SimplexCategory.reedyOp (GeneratedFramings.rightFactor e).i Y j (trivialCofibrations C)).mp
      ((GeneratedFramings.rightFactor e).hi j Y)

end FrameChoices

/-- The whole original coaugmentation retains the original constant unit and right-resolution word.
-/
theorem coaugmentation_eq {κ : Cardinal.{wF}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (e : CofibrantGenerationData C κ) (Y : C) :
    (GeneratedFramings.coaugmentation e).app Y =
      (SimplicialObject.const C).map ((unit e).app Y) ≫ (GeneratedFramings.rightResolution e).app
        Y := by
  apply NatTrans.ext
  funext j
  exact GeneratedFramings.coaugmentation_app e Y j

section FrameChoices

variable {κF : Cardinal.{wF}} [Fact κF.IsRegular] [OrderBot κF.ord.ToType]
  (e : CofibrantGenerationData C κF)

/-- The original coaugmentation is an actual model trivial cofibration with independent
replacements. -/
theorem coaugmentation_model_trivialCofibration (Y : C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((GeneratedFramings.coaugmentation e).app Y) := by
  let _ := simplicialModel d
  rw [coaugmentation_eq e Y]
  exact (trivialCofibrations (SimplicialObject C)).comp_mem _ _
    (constant_unit_trivialCofibration d e Y) (rightResolution_model_trivialCofibration d e Y)

/-- The unchanged original bifibrant-from-Q map is an actual model trivial cofibration. -/
theorem bifibrantFromQ_model_trivialCofibration (X : C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((GeneratedFramings.bifibrantFromQ e).app X) :=
  coaugmentation_model_trivialCofibration d e ((Q e).obj X)

end FrameChoices

end HomotopicalAlgebra.GeneratedFramingModels

end
end
end

section



/-!
# Actual natural comparisons of independent generated right frames

The original two coaugmentations form a functorial pushout. The same original
generated Reedy fibration factory factors its terminal natural map. Both frame
choices compare to the resulting actual fibrant, homotopically constant functor,
retaining every original coefficient map and coaugmentation triangle.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wD wE uC vC

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedFramingChoices

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  (d : CofibrantGenerationData C κD) (e : CofibrantGenerationData C κE)

open GeneratedFramings GeneratedFramingModels

/-- The actual functorial pushout of the two original constant-object coaugmentations. -/
def center : C ⥤ SimplicialObject C := pushout (coaugmentation d) (coaugmentation e)

/-- The full original first pushout leg retains every original first-frame coefficient map. -/
abbrev centerLeft : rightFrame d ⟶ center d e := pushout.inl (coaugmentation d) (coaugmentation e)

/-- The full original second pushout leg retains every original second-frame coefficient map. -/
abbrev centerRight : rightFrame e ⟶ center d e := pushout.inr (coaugmentation d) (coaugmentation e)

/-- The actual first pushout leg is a model trivial cofibration at every original object. -/
theorem centerLeft_trivialCofibration (X : C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((centerLeft d e).app X) := by
  let _ := simplicialModel d
  have h : ((trivialCofibrations (SimplicialObject C)).functorCategory C) (centerLeft d e) :=
    ((trivialCofibrations (SimplicialObject C)).functorCategory C).pushout_inl
      (coaugmentation d) (coaugmentation e) (fun Y => coaugmentation_model_trivialCofibration d e Y)
  exact h X

/-- The actual second pushout leg is a model trivial cofibration at every original object. -/
theorem centerRight_trivialCofibration (X : C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((centerRight d e).app X) := by
  let _ := simplicialModel d
  have h : ((trivialCofibrations (SimplicialObject C)).functorCategory C) (centerRight d e) :=
    ((trivialCofibrations (SimplicialObject C)).functorCategory C).pushout_inr
      (coaugmentation d) (coaugmentation e) (fun Y => coaugmentation_model_trivialCofibration d d Y)
  exact h X

/-- The original terminal natural map of the actual pushout functor. -/
def centerTerminal :
    letI := simplicialModel d
    center d e ⟶ (Functor.const C).obj (⊤_ (SimplicialObject C)) := by
  let _ := simplicialModel d
  exact
    { app X := terminal.from ((center d e).obj X)
      naturality X Y f := by simp }

/-- The same original generated Reedy factory factors the whole terminal map without a
functor-category model. -/
def factor :
    letI := simplicialModel d
    MapFactorizationData ((trivialCofibrations (SimplicialObject C)).functorCategory C)
      ((fibrations (SimplicialObject C)).functorCategory C) (centerTerminal d e) := by
  let _ := simplicialModel d
  exact ((simplicialFibrantFactorizationData d).functorCategory C).factorizationData (centerTerminal
    d e)

/-- The actual middle functor of the original generated Reedy terminal factor. -/
abbrev commonFrame : C ⥤ SimplicialObject C := by
  let _ := simplicialModel d
  exact (factor d e).Z

/-- The first natural comparison retains the original pushout leg and full generated factor map. -/
def comparisonLeft : rightFrame d ⟶ commonFrame d e := by
  let _ := simplicialModel d
  exact centerLeft d e ≫ (factor d e).i

/-- The second natural comparison retains the original pushout leg and full generated factor map. -/
def comparisonRight : rightFrame e ⟶ commonFrame d e := by
  let _ := simplicialModel d
  exact centerRight d e ≫ (factor d e).i

/-- The common coaugmentation is the whole original first coaugmentation and comparison. -/
def commonCoaugmentation : SimplicialObject.const C ⟶ commonFrame d e :=
  coaugmentation d ≫ comparisonLeft d e

/-- Both complete original coaugmentations have the same actual common comparison word. -/
theorem commonCoaugmentation_eq :
    commonCoaugmentation d e = coaugmentation e ≫ comparisonRight d e := by
  let _ := simplicialModel d
  change _ ≫ (_ ≫ (factor d e).i) = _ ≫ (_ ≫ (factor d e).i)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun a : SimplicialObject.const C ⟶ center d e => a ≫ (factor d e).i)
    (pushout.condition (f := coaugmentation d) (g := coaugmentation e))

/-- Every first-branch coordinate retains the original R unit and complete first frame resolution.
-/
theorem commonCoaugmentation_app_left (X : C) (j : SimplexCategoryᵒᵖ) :
    ((commonCoaugmentation d e).app X).app j =
      (GeneratedFunctorialReplacements.unit d).app X ≫ ((rightResolution d).app X).app j ≫
        ((comparisonLeft d e).app X).app j := by
  change ((coaugmentation d).app X).app j ≫ ((comparisonLeft d e).app X).app j = _
  rw [coaugmentation_app]
  exact Category.assoc _ _ _

/-- Every second-branch coordinate retains the original R unit and complete second frame resolution.
-/
theorem commonCoaugmentation_app_right (X : C) (j : SimplexCategoryᵒᵖ) :
    ((commonCoaugmentation d e).app X).app j =
      (GeneratedFunctorialReplacements.unit e).app X ≫ ((rightResolution e).app X).app j ≫
        ((comparisonRight d e).app X).app j := by
  rw [commonCoaugmentation_eq]
  change ((coaugmentation e).app X).app j ≫ ((comparisonRight d e).app X).app j = _
  rw [coaugmentation_app]
  exact Category.assoc _ _ _

/-- The first actual frame comparison is a trivial cofibration in the selected original Reedy model.
-/
theorem comparisonLeft_trivialCofibration (X : C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((comparisonLeft d e).app X) := by
  let _ := simplicialModel d
  exact (trivialCofibrations (SimplicialObject C)).comp_mem _ _
    (centerLeft_trivialCofibration d e X) ((factor d e).hi X)

/-- The second actual frame comparison is a trivial cofibration in the same original Reedy model. -/
theorem comparisonRight_trivialCofibration (X : C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((comparisonRight d e).app X) := by
  let _ := simplicialModel d
  exact (trivialCofibrations (SimplicialObject C)).comp_mem _ _
    (centerRight_trivialCofibration d e X) ((factor d e).hi X)

/-- The actual common coaugmentation is a whole model trivial cofibration at every original object.
-/
theorem commonCoaugmentation_trivialCofibration (X : C) :
    letI := simplicialModel d
    trivialCofibrations (SimplicialObject C) ((commonCoaugmentation d e).app X) := by
  let _ := simplicialModel d
  exact (trivialCofibrations (SimplicialObject C)).comp_mem _ _
    (coaugmentation_model_trivialCofibration d d X) (comparisonLeft_trivialCofibration d e X)

/-- Every common-frame object is fibrant by the same full original terminal factor. -/
theorem commonFrame_isFibrant (X : C) :
    letI := simplicialModel d
    IsFibrant ((commonFrame d e).obj X) := by
  let _ := simplicialModel d
  exact (isFibrant_iff_of_isTerminal ((factor d e).p.app X) terminalIsTerminal).mpr
    ((fibration_iff _).mpr ((factor d e).hp X))

/-- The first natural comparison is weak in every original simplex degree. -/
theorem comparisonLeft_component_weak (X : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((comparisonLeft d e).app X).app j) := by
  let _ := simplicialModel d
  have h := (comparisonLeft_trivialCofibration d e X).2
  change ∀ j, weakEquivalences C (((comparisonLeft d e).app X).app j) at h
  exact h j

/-- The second natural comparison is weak in every original simplex degree. -/
theorem comparisonRight_component_weak (X : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((comparisonRight d e).app X).app j) := by
  let _ := simplicialModel d
  have h := (comparisonRight_trivialCofibration d e X).2
  change ∀ j, weakEquivalences C (((comparisonRight d e).app X).app j) at h
  exact h j

/-- The entire common coaugmentation is weak in every original simplex degree. -/
theorem commonCoaugmentation_component_weak (X : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((commonCoaugmentation d e).app X).app j) := by
  let _ := simplicialModel d
  have h := (commonCoaugmentation_trivialCofibration d e X).2
  change ∀ j, weakEquivalences C (((commonCoaugmentation d e).app X).app j) at h
  exact h j

/-- Every actual common-frame structure map is weak from the same original natural coaugmentation.
-/
theorem commonFrame_structure_weak (X : C) {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    weakEquivalences C (((commonFrame d e).obj X).map f) := by
  have h : ((commonCoaugmentation d e).app X).app i ≫ ((commonFrame d e).obj X).map f =
      ((commonCoaugmentation d e).app X).app j := by
    simpa using (((commonCoaugmentation d e).app X).naturality f).symm
  exact (weakEquivalences C).of_precomp _ _ (commonCoaugmentation_component_weak d e X i)
    (h.symm ▸ commonCoaugmentation_component_weak d e X j)

/-- Every actual common-frame matching map is a source fibration in the same original coefficient
model. -/
theorem commonFrame_matching_fibration (X : C) (j : SimplexCategoryᵒᵖ) :
    fibrations C (CategoryTheory.ReedyStructure.matchingMap SimplexCategory.reedyOp ((commonFrame d
      e).obj X) j) := by
  let _ := simplicialModel d
  exact (fibration_iff _).mp ((simplicial_isFibrant_iff d _).mp (commonFrame_isFibrant d e X) j)

end HomotopicalAlgebra.GeneratedFramingChoices

end
end
end

section



/-!
# Original coefficient weak maps under the actual generated frames

The actual left and right resolution squares compare every original coefficient
map with the same original Q or R map. Two-out-of-three therefore gives weak
preservation degree by degree, retaining the complete original frame maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory

namespace HomotopicalAlgebra.GeneratedFramings

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The original left resolution square proves weakness of every original coefficient frame map. -/
theorem leftFrame_coefficient_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f)
    (j : SimplexCategory) : weakEquivalences C (((leftFrame d).map f).app j) := by
  let _ : WeakEquivalence ((Q d).map f) := (weakEquivalence_iff _).mpr (Q_map_weak d f hf)
  let _ : WeakEquivalence (((leftResolution d).app X).app j) :=
    (weakEquivalence_iff _).mpr (leftResolution_weak d X j)
  let _ : WeakEquivalence (((leftResolution d).app Y).app j) :=
    (weakEquivalence_iff _).mpr (leftResolution_weak d Y j)
  have h : ((leftFrame d).map f).app j ≫ ((leftResolution d).app Y).app j =
      ((leftResolution d).app X).app j ≫ (Q d).map f := by
    exact congrArg (fun t => t.app j) ((leftResolution d).naturality f)
  let _ : WeakEquivalence (((leftFrame d).map f).app j) := weakEquivalence_of_postcomp_of_fac h
  exact mem_weakEquivalences _

/-- The original right resolution square proves weakness of every original coefficient frame map. -/
theorem rightFrame_coefficient_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f)
    (j : SimplexCategoryᵒᵖ) : weakEquivalences C (((rightFrame d).map f).app j) := by
  let _ : WeakEquivalence ((R d).map f) := (weakEquivalence_iff _).mpr (R_map_weak d f hf)
  let _ : WeakEquivalence (((rightResolution d).app X).app j) :=
    (weakEquivalence_iff _).mpr (rightResolution_weak d X j)
  let _ : WeakEquivalence (((rightResolution d).app Y).app j) :=
    (weakEquivalence_iff _).mpr (rightResolution_weak d Y j)
  have h : ((rightResolution d).app X).app j ≫ ((rightFrame d).map f).app j =
      (R d).map f ≫ ((rightResolution d).app Y).app j := by
    exact (congrArg (fun t => t.app j) ((rightResolution d).naturality f)).symm
  let _ : WeakEquivalence (((rightFrame d).map f).app j) := weakEquivalence_of_precomp_of_fac h
  exact mem_weakEquivalences _

/-- The same original Q map followed by the same right frame preserves every coefficient weak map.
-/
theorem bifibrantFrame_coefficient_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f)
    (j : SimplexCategoryᵒᵖ) : weakEquivalences C (((bifibrantFrame d).map f).app j) :=
  rightFrame_coefficient_weak d ((Q d).map f) (Q_map_weak d f hf) j

end HomotopicalAlgebra.GeneratedFramings

end
end
end

section



/-!
# Original coefficient weak maps in the genuine simplicial Reedy model

Every comparison uses the same original coefficient map in every degree. The
actual model weak class is objectwise, so the already-proved frame and common
coaugmentation equations give full model weak preservation without extra
completeness or a mapping-invariance assumption.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wF uC vC

open CategoryTheory

namespace HomotopicalAlgebra.GeneratedFramingModels

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
  (d : CofibrantGenerationData C κM)

/-- Every original coefficient weak map is weak on the complete original constant diagram. -/
theorem constant_model_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    letI := simplicialModel d
    WeakEquivalence ((SimplicialObject.const C).map f) := by
  let _ := simplicialModel d
  apply (weakEquivalence_iff _).mpr
  change ∀ j : SimplexCategoryᵒᵖ, weakEquivalences C f
  exact fun _ => hf

variable {κF : Cardinal.{wF}} [Fact κF.IsRegular] [OrderBot κF.ord.ToType]
  (e : CofibrantGenerationData C κF)

/-- The whole original right-frame coefficient map is weak in the actual selected diagram model. -/
theorem rightFrame_model_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    letI := simplicialModel d
    WeakEquivalence ((GeneratedFramings.rightFrame e).map f) := by
  let _ := simplicialModel d
  apply (weakEquivalence_iff _).mpr
  change ∀ j, weakEquivalences C (((GeneratedFramings.rightFrame e).map f).app j)
  exact GeneratedFramings.rightFrame_coefficient_weak e f hf

/-- The whole original bifibrant-frame map is weak for independent model and replacement choices. -/
theorem bifibrantFrame_model_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    letI := simplicialModel d
    WeakEquivalence ((GeneratedFramings.bifibrantFrame e).map f) := by
  let _ := simplicialModel d
  apply (weakEquivalence_iff _).mpr
  change ∀ j, weakEquivalences C (((GeneratedFramings.bifibrantFrame e).map f).app j)
  exact GeneratedFramings.bifibrantFrame_coefficient_weak e f hf

end HomotopicalAlgebra.GeneratedFramingModels

namespace HomotopicalAlgebra.GeneratedFramingChoices

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
  {κF : Cardinal.{wF}} [Fact κF.IsRegular] [OrderBot κF.ord.ToType]
  (d : CofibrantGenerationData C κM) (e : CofibrantGenerationData C κF)

/-- Every original common-frame coefficient map is weak by its entire original coaugmentation
square. -/
theorem commonFrame_coefficient_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f)
    (j : SimplexCategoryᵒᵖ) : weakEquivalences C (((commonFrame d e).map f).app j) := by
  have h : ((commonCoaugmentation d e).app X).app j ≫ ((commonFrame d e).map f).app j =
      f ≫ ((commonCoaugmentation d e).app Y).app j :=
    (congrArg (fun t => t.app j) ((commonCoaugmentation d e).naturality f)).symm
  exact (weakEquivalences C).of_precomp _ _ (commonCoaugmentation_component_weak d e X j)
    (h.symm ▸ (weakEquivalences C).comp_mem _ _ hf (commonCoaugmentation_component_weak d e Y j))

/-- The full original common-frame coefficient map is weak in the same generated diagram model. -/
theorem commonFrame_model_weak {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    letI := GeneratedFramingModels.simplicialModel d
    WeakEquivalence ((commonFrame d e).map f) := by
  let _ := GeneratedFramingModels.simplicialModel d
  apply (weakEquivalence_iff _).mpr
  change ∀ j, weakEquivalences C (((commonFrame d e).map f).app j)
  exact commonFrame_coefficient_weak d e f hf

end HomotopicalAlgebra.GeneratedFramingChoices

end
end
end

section



/-!
# Actual good cylinders and path objects from the original generated framings

The original degree-one boundary comparisons identify the actual latching map with the
ordered coface coproduct and the actual matching map with the ordered face product.
The generated-frame class and weak-constancy proofs therefore construct good cylinders
and paths with the same original Q/R endpoints, degree-one objects, and structure maps.
No framing or homotopy-function-complex outcome is supplied as an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty Simplicial

namespace HomotopicalAlgebra.GeneratedFramings

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The original cosimplicial codegeneracy and same degree-zero Q identification form a weak
retraction. -/
theorem leftCylinder_projection_weak (X : C) :
    weakEquivalences C (((leftFrame d).obj X).σ (0 : Fin 1) ≫
      (leftZeroIso d).hom.app X) :=
  (weakEquivalences C).comp_mem _ _
    (leftFrame_map_weak d X (SimplexCategory.σ (0 : Fin 1)))
    ((weakEquivalences C).of_isIso _)

/-- The actual original degree-one coproduct inclusion at the same Q endpoint is a cofibration. -/
theorem leftCylinder_inclusion_cofibration (X : C) :
    cofibrations C (coprod.desc
      ((leftZeroIso d).inv.app X ≫ ((leftFrame d).obj X).δ (0 : Fin 2))
      ((leftZeroIso d).inv.app X ≫ ((leftFrame d).obj X).δ (1 : Fin 2))) := by
  let A := (leftFrame d).obj X
  let e := (leftZeroIso d).app X
  have hA : cofibrations C (SimplexCategory.reedy.latchingMap A ⦋1⦌) :=
    leftFrame_latching_cofibration d X ⦋1⦌
  let _ : IsIso (coprod.map e.inv e.inv) := by infer_instance
  have hpair : cofibrations C (coprod.desc (A.δ (0 : Fin 2)) (A.δ (1 : Fin 2))) :=
    FramingDegreeOneBoundaries.cosimplicialLatchingOneIso_inv_map A ▸
      (cofibrations C).comp_mem _ _ ((cofibrations C).of_isIso _) hA
  have he : coprod.map e.inv e.inv ≫ coprod.desc (A.δ (0 : Fin 2)) (A.δ (1 : Fin 2)) =
      coprod.desc (e.inv ≫ A.δ (0 : Fin 2)) (e.inv ≫ A.δ (1 : Fin 2)) :=
    coprod.map_desc (A.δ (0 : Fin 2)) (A.δ (1 : Fin 2)) e.inv e.inv
  exact he ▸ (cofibrations C).comp_mem _ _ ((cofibrations C).of_isIso _) hpair

/-- The original simplicial degeneracy and same degree-zero R identification form a weak section. -/
theorem rightPath_section_weak (X : C) :
    weakEquivalences C ((rightZeroIso d).hom.app X ≫
      ((rightFrame d).obj X).σ (0 : Fin 1)) :=
  (weakEquivalences C).comp_mem _ _ ((weakEquivalences C).of_isIso _)
    (rightFrame_map_weak d X (SimplexCategory.σ (0 : Fin 1)).op)

/-- The actual original degree-one ordered product projection to the same R endpoint is a fibration.
-/
theorem rightPath_projection_fibration (X : C) :
    fibrations C (prod.lift
      (((rightFrame d).obj X).δ (0 : Fin 2) ≫ (rightZeroIso d).inv.app X)
      (((rightFrame d).obj X).δ (1 : Fin 2) ≫ (rightZeroIso d).inv.app X)) := by
  let B := (rightFrame d).obj X
  let e := (rightZeroIso d).app X
  have hB : fibrations C (SimplexCategory.reedyOp.matchingMap B (Opposite.op
    ⦋1⦌)) :=
    rightFrame_matching_fibration d X (Opposite.op ⦋1⦌)
  let _ : IsIso (prod.map e.inv e.inv) := by infer_instance
  rw [← prod.lift_map, ← FramingDegreeOneBoundaries.simplicialMatchingOneIso_map_hom B]
  exact (fibrations C).comp_mem _ _
    ((fibrations C).comp_mem _ _ hB ((fibrations C).of_isIso _)) ((fibrations C).of_isIso _)

/-- The actual original-Q good cylinder uses the same frame object and original structure maps. -/
def leftCylinder (X : C) : Cylinder ((Q d).obj X) := by
  let A := (leftFrame d).obj X
  let e := ((leftZeroIso d).app X).symm
  letI : WeakEquivalence (A.σ (0 : Fin 1) ≫ e.inv) :=
    (weakEquivalence_iff _).mpr (leftCylinder_projection_weak d X)
  exact ResolutionHomComplex.LeftPiZero.cylinder A e

/-- The actual original-R path object uses the same frame object and original structure maps. -/
def rightPath (X : C) : PathObject ((R d).obj X) := by
  let B := (rightFrame d).obj X
  let e := (rightZeroIso d).app X
  letI : WeakEquivalence (e.hom ≫ B.σ (0 : Fin 1)) :=
    (weakEquivalence_iff _).mpr (rightPath_section_weak d X)
  exact ResolutionHomComplex.RightPiZero.path B e

/-- The same original degree-one coproduct map makes the actual cylinder good. -/
instance leftCylinder_isGood (X : C) : (leftCylinder d X).IsGood where
  cofibration_i := by
    change Cofibration (coprod.desc
      ((leftZeroIso d).inv.app X ≫ ((leftFrame d).obj X).δ (0 : Fin 2))
      ((leftZeroIso d).inv.app X ≫ ((leftFrame d).obj X).δ (1 : Fin 2)))
    exact (cofibration_iff _).mpr (leftCylinder_inclusion_cofibration d X)

/-- The same original degree-one product map makes the actual path object good. -/
instance rightPath_isGood (X : C) : (rightPath d X).IsGood where
  fibration_p := by
    change Fibration (prod.lift
      (((rightFrame d).obj X).δ (0 : Fin 2) ≫ (rightZeroIso d).inv.app X)
      (((rightFrame d).obj X).δ (1 : Fin 2) ≫ (rightZeroIso d).inv.app X))
    exact (fibration_iff _).mpr (rightPath_projection_fibration d X)

/-- The actual cylinder carrier is the original first cosimplicial frame degree. -/
theorem leftCylinder_I (X : C) : (leftCylinder d X).I = ((leftFrame d).obj X).obj ⦋1⦌ := rfl

/-- The first original cylinder inclusion retains the original coface zero and Q identification. -/
theorem leftCylinder_i₀ (X : C) :
    (leftCylinder d X).i₀ = (leftZeroIso d).inv.app X ≫
      ((leftFrame d).obj X).δ (0 : Fin 2) := rfl

/-- The second original cylinder inclusion retains the original coface one and Q identification. -/
theorem leftCylinder_i₁ (X : C) :
    (leftCylinder d X).i₁ = (leftZeroIso d).inv.app X ≫
      ((leftFrame d).obj X).δ (1 : Fin 2) := rfl

/-- The actual cylinder retraction retains the original codegeneracy and Q identification. -/
theorem leftCylinder_π (X : C) :
    (leftCylinder d X).π = ((leftFrame d).obj X).σ (0 : Fin 1) ≫
      (leftZeroIso d).hom.app X := rfl

/-- The actual path carrier is the original first simplicial frame degree. -/
theorem rightPath_P (X : C) :
    (rightPath d X).P = ((rightFrame d).obj X).obj (Opposite.op ⦋1⦌) := rfl

/-- The first original path projection retains face zero and the R identification. -/
theorem rightPath_p₀ (X : C) :
    (rightPath d X).p₀ = ((rightFrame d).obj X).δ (0 : Fin 2) ≫
      (rightZeroIso d).inv.app X := rfl

/-- The second original path projection retains face one and the R identification. -/
theorem rightPath_p₁ (X : C) :
    (rightPath d X).p₁ = ((rightFrame d).obj X).δ (1 : Fin 2) ≫
      (rightZeroIso d).inv.app X := rfl

/-- The actual path section retains the original degeneracy and R identification. -/
theorem rightPath_ι (X : C) :
    (rightPath d X).ι = (rightZeroIso d).hom.app X ≫
      ((rightFrame d).obj X).σ (0 : Fin 1) := rfl

/-- Every original Q morphism preserves the first actual generated cylinder inclusion. -/
theorem leftCylinder_i₀_naturality {X Y : C} (f : X ⟶ Y) :
    (Q d).map f ≫ (leftCylinder d Y).i₀ =
      (leftCylinder d X).i₀ ≫ ((leftFrame d).map f).app ⦋1⦌ :=
  ((leftZeroIso d).inv ≫ Functor.whiskerLeft (leftFrame d)
    ((evaluation SimplexCategory C).map (SimplexCategory.δ (0 : Fin 2)))).naturality f

/-- Every original Q morphism preserves the second actual generated cylinder inclusion. -/
theorem leftCylinder_i₁_naturality {X Y : C} (f : X ⟶ Y) :
    (Q d).map f ≫ (leftCylinder d Y).i₁ =
      (leftCylinder d X).i₁ ≫ ((leftFrame d).map f).app ⦋1⦌ :=
  ((leftZeroIso d).inv ≫ Functor.whiskerLeft (leftFrame d)
    ((evaluation SimplexCategory C).map (SimplexCategory.δ (1 : Fin 2)))).naturality f

/-- Every original Q morphism preserves the actual generated cylinder retraction. -/
theorem leftCylinder_π_naturality {X Y : C} (f : X ⟶ Y) :
    ((leftFrame d).map f).app ⦋1⦌ ≫ (leftCylinder d Y).π =
      (leftCylinder d X).π ≫ (Q d).map f :=
  (Functor.whiskerLeft (leftFrame d)
    ((evaluation SimplexCategory C).map (SimplexCategory.σ (0 : Fin 1))) ≫
      (leftZeroIso d).hom).naturality f

/-- Every original R morphism preserves the first actual generated path projection. -/
theorem rightPath_p₀_naturality {X Y : C} (f : X ⟶ Y) :
    ((rightFrame d).map f).app (Opposite.op ⦋1⦌) ≫ (rightPath d Y).p₀ =
      (rightPath d X).p₀ ≫ (R d).map f :=
  (Functor.whiskerLeft (rightFrame d)
    ((evaluation SimplexCategoryᵒᵖ C).map (SimplexCategory.δ (0 : Fin 2)).op) ≫
      (rightZeroIso d).inv).naturality f

/-- Every original R morphism preserves the second actual generated path projection. -/
theorem rightPath_p₁_naturality {X Y : C} (f : X ⟶ Y) :
    ((rightFrame d).map f).app (Opposite.op ⦋1⦌) ≫ (rightPath d Y).p₁ =
      (rightPath d X).p₁ ≫ (R d).map f :=
  (Functor.whiskerLeft (rightFrame d)
    ((evaluation SimplexCategoryᵒᵖ C).map (SimplexCategory.δ (1 : Fin 2)).op) ≫
      (rightZeroIso d).inv).naturality f

/-- Every original R morphism preserves the actual generated path section. -/
theorem rightPath_ι_naturality {X Y : C} (f : X ⟶ Y) :
    (R d).map f ≫ (rightPath d Y).ι =
      (rightPath d X).ι ≫ ((rightFrame d).map f).app (Opposite.op ⦋1⦌) :=
  ((rightZeroIso d).hom ≫ Functor.whiskerLeft (rightFrame d)
    ((evaluation SimplexCategoryᵒᵖ C).map (SimplexCategory.σ (0 : Fin 1)).op)).naturality f

end HomotopicalAlgebra.GeneratedFramings

end
end
end

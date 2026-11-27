/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralEtaleCoherentFamilies
public import MathlibExt.AlgebraicGeometry.GeneralArcHypercoverModels
public import MathlibExt.AlgebraicTopology.NativeInitialSectionModels

/-!
# Actual categorical coefficient hypercover comparisons

The augmentation is the original over-object map to the base scheme.
The categorical limit is the full native cocartesian section object
over the whole scheme diagram. Its comparison is the inverse of the
original initial-index evaluation followed by actual section restriction.
No supplied limit/comparison callback or maximal core replaces a category.

Constructible and fixed-amplitude categories are the original full
enhanced coefficient families. They retain arbitrary finite coefficient
rings, including noncommutative rings, and general qcqs schemes.

Source: Bhatt--Mathew1807.04725v4, Notation5.8 and Theorem5.13;
native categorical sections and HTT Section3.3.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralCoefficientHyperdescentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open GeneralArcCoverModels GeneralArcHypercoverModels GeneralEtaleCoherentFamilies
open GeneralEtaleCoefficientModels GeneralEtalePullbackCoherence
open DerivedCoefficientImageModels SimplicialDerivedModels
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicTopology.NativeInitialSectionModels
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open scoped Simplicial

abbrev AugmentedIndex := (WithTerminal SimplexCategoryᵒᵖ)ᵒᵖ
abbrev UnaugmentedIndex := (SimplexCategoryᵒᵖ)ᵒᵖ

/-- The native whole unaugmented index inclusion. -/
def indexInclusion : UnaugmentedIndex ⥤ AugmentedIndex :=
  (WithTerminal.incl (C := SimplexCategoryᵒᵖ)).op

/-- Lift the entire original index map into the coefficient family's value universe. -/
def liftedIndexInclusion : liftSet.{0, 2} (nerve UnaugmentedIndex) ⟶
    liftSet.{0, 2} (nerve AugmentedIndex) :=
  (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{2}).map (nerveMap indexInclusion)

/-- The original initial augmentation vertex. -/
def augmentationVertex : (liftSet.{0, 2} (nerve AugmentedIndex)) _⦋0⦌ :=
  ULift.up (ComposableArrows.mk₀ (op (WithTerminal.star : WithTerminal SimplexCategoryᵒᵖ)))

/-- The actual base scheme vertex in the original coefficient base nerve. -/
def schemeBaseVertex (X : QcqsScheme) : BaseSet _⦋0⦌ :=
  ULift.up (ComposableArrows.mk₀ (op X))

variable {X : QcqsScheme} (H : SimplicialObject (Over X))

/-- The full original augmented base map. -/
def augmentedBase : liftSet.{0, 2} (nerve AugmentedIndex) ⟶ BaseSet :=
  diagramBaseMap (augmentedDiagram H).op

/-- The full original unaugmented base map. -/
def unaugmentedBase : liftSet.{0, 2} (nerve UnaugmentedIndex) ⟶ BaseSet :=
  diagramBaseMap (underlyingDiagram H).op

/-- Native restriction is the original whole scheme-diagram restriction. -/
theorem base_restriction : liftedIndexInclusion ≫ augmentedBase H = unaugmentedBase H := by
  ext n a
  apply congrArg ULift.up
  have he := congrArg _root_.CategoryTheory.Functor.op (augmentation_restriction H)
  change (a.down ⋙ indexInclusion) ⋙ (augmentedDiagram H).op =
    a.down ⋙ (underlyingDiagram H).op
  rw [_root_.CategoryTheory.Functor.assoc]
  exact congrArg (fun F => a.down ⋙ F) he

/-- The augmentation point is exactly the original base scheme. -/
theorem augmentation_base : baseVertex (augmentedBase H) augmentationVertex = schemeBaseVertex X := rfl

/-- Actual full section restriction on every parameter simplex. -/
def hypercoverRestriction {E : SSet.{2}} (p : E ⟶ BaseSet) :
    sectionsOver p (augmentedBase H) ⟶ sectionsOver p (unaugmentedBase H) :=
  sectionsOverMap p (augmentedBase H) (unaugmentedBase H) liftedIndexInclusion (base_restriction H)

/-- The source comparison uses only the inverse of the fixed native initial-index evaluation. -/
structure HypercoverComparisonSource {E : SSet.{2}} (p : E ⟶ BaseSet) where
  initial : InitialSectionComparison p (augmentedBase H) augmentationVertex

/-- The comparison is that native inverse followed by original whole-diagram restriction. -/
def hypercoverComparison {E : SSet.{2}} (p : E ⟶ BaseSet)
    (I : HypercoverComparisonSource H p) :
    fibre p (schemeBaseVertex X) ⟶ sectionsOver p (unaugmentedBase H) :=
  eqToHom (congrArg (fibre p) (augmentation_base H).symm) ≫
    I.initial.inverse ≫ hypercoverRestriction H p

variable (Λ : Type) [Ring Λ]
  [∀ Y : _root_.AlgebraicGeometry.Scheme.{0},
    HasSheafify Y.smallEtaleTopology (ModuleCat.{1} Λ)]
  (S : ∀ {Y Z : _root_.AlgebraicGeometry.Scheme.{0}} (f : Y ⟶ Z), EtalePullbackSource Λ f)
  (U : ∀ Y : _root_.AlgebraicGeometry.Scheme.{0},
    EtaleComplexesPullbackCoherence.EtaleBaseChangeUnitSource Y)
  (C : CoefficientPseudofunctorSource Λ S U) (D : DerivedCoefficientFamily Λ S U C)

/-- The actual full derived constructible coefficient category on X. -/
def constructibleFibre (X : QcqsScheme) : SSet.{2} :=
  fibre (constructibleProjection Λ S U C D) (schemeBaseVertex X)

/-- The source fixed-amplitude family has the same actual original cochain condition. -/
def amplitudeProjection (n : ℕ) : amplitudeFamily Λ S U C D (-(n : ℤ)) (n : ℤ) ⟶ BaseSet :=
  (D.total.fullEnhancedSubcategory (IsAmplitudeVertex Λ S U C D (-(n : ℤ)) (n : ℤ))).ι ≫ D.projection

/-- Its fibre is the actual full category, retaining every noninvertible module map. -/
def amplitudeFibre (X : QcqsScheme) (n : ℕ) : SSet.{2} :=
  fibre (amplitudeProjection Λ S U C D n) (schemeBaseVertex X)

/-- The actual source constructible hypercover comparison. -/
def constructibleComparison
    (I : HypercoverComparisonSource H (constructibleProjection Λ S U C D)) :
    constructibleFibre Λ S U C D X ⟶ constructibleLimit Λ S U C D (underlyingDiagram H).op :=
  hypercoverComparison H (constructibleProjection Λ S U C D) I

/-- The actual source fixed-amplitude hypercover comparison. -/
def amplitudeComparison (n : ℕ)
    (I : HypercoverComparisonSource H (amplitudeProjection Λ S U C D n)) :
    amplitudeFibre Λ S U C D X n ⟶ sectionsOver
      (amplitudeProjection Λ S U C D n) (unaugmentedBase H) :=
  hypercoverComparison H (amplitudeProjection Λ S U C D n) I

end MathlibExt.AlgebraicGeometry.GeneralCoefficientHyperdescentModels

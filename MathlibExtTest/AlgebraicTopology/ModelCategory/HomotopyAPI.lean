/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPushout
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFunctionComplex
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedHomotopyFunctionComplex

public meta section

/-!
# Public homotopy foundations integration clients

These clients retain every supplied map and universal square. The ordinary
comparison cases exercise both asymmetric leg choices and distinguish proper
model hypotheses from cofibrant/fibrant endpoint hypotheses. Frame and path
clients use the actual supplied factorization data.
-/

set_option autoImplicit false
noncomputable section

universe u v
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.HomotopyAPI

variable {C : Type u} [Category.{v} C] [ModelCategory C]

section Properness

example [IsLeftProper C] {A B X Y : C}
    (i : A ⟶ B) (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (square : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] :
    WeakEquivalence f' :=
  IsLeftProper.weakEquivalence_of_isPushout square

example [IsRightProper C] {A B X Y : C}
    (p' : A ⟶ B) (f' : A ⟶ X) (f : B ⟶ Y) (p : X ⟶ Y)
    (square : IsPullback p' f' f p) [Fibration p] [WeakEquivalence f] :
    WeakEquivalence f' :=
  IsRightProper.weakEquivalence_of_isPullback square

example (allCofibrant : ∀ X : C, IsCofibrant X) : IsLeftProper C :=
  isLeftProper_of_all_objects_cofibrant allCofibrant

example (allFibrant : ∀ X : C, IsFibrant X) : IsRightProper C :=
  isRightProper_of_all_objects_fibrant allFibrant

end Properness

section Pushouts

variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

example {F G : WalkingSpan ⥤ C} (maps : F ⟶ G)
    (weak : ∀ j, WeakEquivalence (maps.app j)) :
    WeakEquivalence ((homotopyPushout (C := C)).map maps) :=
  homotopyPushout_map_weakEquivalence maps weak

example (F : WalkingSpan ⥤ C) [IsCofibrant (F.obj WalkingSpan.zero)]
    [IsCofibrant (F.obj WalkingSpan.right)] [Cofibration (F.map WalkingSpan.Hom.fst)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app F) :=
  weakEquivalence_homotopyPushoutComparison_of_fst F

example (F : WalkingSpan ⥤ C) [IsCofibrant (F.obj WalkingSpan.zero)]
    [IsCofibrant (F.obj WalkingSpan.left)] [Cofibration (F.map WalkingSpan.Hom.snd)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app F) :=
  weakEquivalence_homotopyPushoutComparison_of_snd F

example [IsLeftProper C] (F : WalkingSpan ⥤ C)
    [Cofibration (F.map WalkingSpan.Hom.fst)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app F) :=
  weakEquivalence_homotopyPushoutComparison_of_leftProper_fst F

example [IsLeftProper C] (F : WalkingSpan ⥤ C)
    [Cofibration (F.map WalkingSpan.Hom.snd)] :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app F) :=
  weakEquivalence_homotopyPushoutComparison_of_leftProper_snd F

example (F : WalkingSpan ⥤ C) (replacement : CofibrantSpanReplacement F) :
    WeakEquivalence ((homotopyPushoutComparison (C := C)).app F) ↔
      WeakEquivalence replacement.toPushout :=
  replacement.weakEquivalence_homotopyPushoutComparison_iff

end Pushouts

section Pullbacks

variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

example {F G : WalkingCospan ⥤ C} (maps : F ⟶ G)
    (weak : ∀ j, WeakEquivalence (maps.app j)) :
    WeakEquivalence ((homotopyPullback (C := C)).map maps) :=
  homotopyPullback_map_weakEquivalence maps weak

example (F : WalkingCospan ⥤ C) [IsFibrant (F.obj WalkingCospan.one)]
    [IsFibrant (F.obj WalkingCospan.right)] [Fibration (F.map WalkingCospan.Hom.inl)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app F) :=
  weakEquivalence_homotopyPullbackComparison_of_inl F

example (F : WalkingCospan ⥤ C) [IsFibrant (F.obj WalkingCospan.one)]
    [IsFibrant (F.obj WalkingCospan.left)] [Fibration (F.map WalkingCospan.Hom.inr)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app F) :=
  weakEquivalence_homotopyPullbackComparison_of_inr F

example [IsRightProper C] (F : WalkingCospan ⥤ C)
    [Fibration (F.map WalkingCospan.Hom.inl)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app F) :=
  weakEquivalence_homotopyPullbackComparison_of_rightProper_inl F

example [IsRightProper C] (F : WalkingCospan ⥤ C)
    [Fibration (F.map WalkingCospan.Hom.inr)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app F) :=
  weakEquivalence_homotopyPullbackComparison_of_rightProper_inr F

example (F : WalkingCospan ⥤ C) (replacement : FibrantCospanReplacement F) :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app F) ↔
      WeakEquivalence replacement.fromPullback :=
  replacement.weakEquivalence_homotopyPullbackComparison_iff

end Pullbacks

section GivenPathsAndFrames

example (factor : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : C) :
    (PathObject.ofFactorizationData (factor.factorizationData (diag X))).IsVeryGood :=
  inferInstance

example (factor : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : C) :
    (PathObject.ofFactorizationData (factor.factorizationData (diag X))).ι ≫
      (PathObject.ofFactorizationData (factor.factorizationData (diag X))).p₀ = 𝟙 X :=
  (PathObject.ofFactorizationData (factor.factorizationData (diag X))).toPrepathObject.ι_p₀

example (factor : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (X : C) :
    (Cylinder.ofFactorizationData (factor.factorizationData (codiag X))).IsVeryGood :=
  inferInstance

example (factor : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (X : C) :
    (Cylinder.ofFactorizationData (factor.factorizationData (codiag X))).i₀ ≫
      (Cylinder.ofFactorizationData (factor.factorizationData (codiag X))).π = 𝟙 X :=
  (Cylinder.ofFactorizationData (factor.factorizationData (codiag X))).toPrecylinder.i₀_π

example (data : GeneratedFunctorialReplacements.Data (C := C)) (X : C)
    (degree : SimplexCategory) :
    cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy
      ((FunctorialFramings.leftFrame data).obj X) degree) :=
  FunctorialFramings.leftFrame_latching_cofibration data X degree

example (data : GeneratedFunctorialReplacements.Data (C := C)) (X : C)
    (degree : SimplexCategoryᵒᵖ) :
    fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((FunctorialFramings.rightFrame data).obj X) degree) :=
  FunctorialFramings.rightFrame_matching_fibration data X degree

end GivenPathsAndFrames

section ExplicitFunctionComplexData

variable [SimplicialCategory C]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- Alternative-presentation tests detect a weak map only through the
explicit invariance, natural comparison, and detection packet. -/
example (data : HomotopyFunctionComplexData (C := C)) {X Y : C} (f : X ⟶ Y)
    (alternativeTests : ∀ Z : C, IsFibrant Z →
      SSet.realizationWeakEquivalences ((data.alternativeMappingObject.map f.op).app Z)) :
    weakEquivalences C f := by
  apply (data.weakEquivalence_iff_derivedMappingPrecomp f).mpr
  intro Z hZ
  exact (derivedMappingPrecomp_weak_iff_alternative data f Z).mpr (alternativeTests Z hZ)

end ExplicitFunctionComplexData

section GeneratedChoiceComparison

universe wD wE
open scoped SSet.modelCategoryQuillen

/-- The generated comparison is actually produced from both supplied
generation records; a comparison or its weakness is not supplied. -/
example {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
    {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
    (first : CofibrantGenerationData C κD) (second : CofibrantGenerationData C κE)
    (X Y : C) :
    WeakEquivalence (((GeneratedMappingChoiceComparisons.left first second).app
      (Opposite.op X)).app Y) :=
  GeneratedMappingChoiceComparisons.left_weak first second X Y

end GeneratedChoiceComparison

end MathlibExtTest.HomotopyAPI

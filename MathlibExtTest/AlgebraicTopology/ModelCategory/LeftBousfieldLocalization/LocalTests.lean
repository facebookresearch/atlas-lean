/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.ObjectProperty.Local
public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Local

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.LeftBousfieldLocalizationLocalTests

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
variable {I : Type w} (S : I → Arrow C)

section Definitions

variable {X Y Z : C}

example : Prop := isDerivedLocal S Z

example : Prop := isLocalFibrant S Z

example : MorphismProperty C := localEquivalences S

example (hZ : isLocalFibrant S Z) (i : I) :
    SSet.realizationWeakEquivalences
      (derivedMappingPrecomp (C := C) (S i).hom Z) :=
  hZ.2 i

/-- Ordinary strict-Hom locality does not inhabit derived simplicial locality. -/
example (W : MorphismProperty C) (_h : W.isLocal Z) : True := by
  fail_if_success exact (_h : isDerivedLocal S Z)
  trivial

end Definitions

section Closure

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
variable (hf : localEquivalences S f) (hg : localEquivalences S g)
variable (hfg : localEquivalences S (f ≫ g))

example : localEquivalences S (𝟙 X) :=
  (localEquivalences_containsIdentities S).id_mem X

example : localEquivalences S (f ≫ g) :=
  (localEquivalences_hasTwoOutOfThreeProperty S).comp_mem f g hf hg

example : localEquivalences S f :=
  (localEquivalences_hasTwoOutOfThreeProperty S).of_postcomp f g hg hfg

example : localEquivalences S g :=
  (localEquivalences_hasTwoOutOfThreeProperty S).of_precomp f g hf hfg

example {X' Y' : C} {f' : X' ⟶ Y'}
    (h : RetractArrow f f') (hf' : localEquivalences S f') :
    localEquivalences S f :=
  (localEquivalences_isStableUnderRetracts S).of_retract h hf'

example (e : X ⟶ Y) [IsIso e] : localEquivalences S e := by
  let _ : (localEquivalences S).ContainsIdentities :=
    localEquivalences_containsIdentities S
  let _ : (localEquivalences S).IsStableUnderRetracts :=
    localEquivalences_isStableUnderRetracts S
  exact (localEquivalences S).of_isIso e

/-- Closure is explicit and is not installed as a global instance. -/
example : True := by
  fail_if_success
    let _ : (localEquivalences S).HasTwoOutOfThreeProperty := by infer_instance
  trivial

end Closure

section WeakInclusionAndDetection

variable (data : HomotopyFunctionComplexData (C := C))
variable {X Y : C} (f : X ⟶ Y)

example (hf : weakEquivalences C f) : localEquivalences S f :=
  weakEquivalences_le_localEquivalences
    data.toHomotopyFunctionComplexInvarianceData.toHomotopyFunctionComplexPrecompData
      S f hf

variable {E : Type w} [IsEmpty E] (emptyFamily : E → Arrow C)

example : localEquivalences emptyFamily = weakEquivalences C :=
  localEquivalences_empty data emptyFamily

/-- Omitting the 17.7.7 detector prevents construction of the packet used by empty-family
recovery. -/
example : True := by
  fail_if_success
    exact (show HomotopyFunctionComplexData (C := C) from
      { alternativeMappingObject := data.alternativeMappingObject
        comparisonMappingObject := data.comparisonMappingObject
        comparisonToDerived := data.comparisonToDerived
        comparisonToAlternative := data.comparisonToAlternative
        comparisonToDerived_weak := data.comparisonToDerived_weak
        comparisonToAlternative_weak := data.comparisonToAlternative_weak
        precompWeakOfWeakEquivalence := data.precompWeakOfWeakEquivalence
        postcompWeakOfWeakEquivalence := data.postcompWeakOfWeakEquivalence })
  trivial

end WeakInclusionAndDetection

section AccessibilityBoundary

variable (accessibility : DerivedLocalityAccessibilityData S)
variable (X Z : C)

example : Functor.IsAccessible.{w}
    ((derivedMappingObject (C := C)).obj (.op X)) :=
  accessibility.fixedSourceAccessible X

example : Functor.IsAccessible.{w}
    (derivedMappingObject (C := C) ⋙ (evaluation C SSet.{v}).obj Z) :=
  accessibility.fixedTargetAccessible Z

example : MorphismProperty.IsAccessible.{w} (localEquivalences S) :=
  accessibility.localEquivalencesAccessible

/-- Homotopical data alone does not install accessibility. -/
example (_data : HomotopyFunctionComplexData (C := C)) : True := by
  fail_if_success
    let _ : MorphismProperty.IsAccessible.{w} (localEquivalences S) := by
      infer_instance
  trivial

end AccessibilityBoundary

section UniverseOneZero

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁]
variable [SimplicialCategory C₁]
variable [HasFunctorialFactorization (cofibrations C₁) (trivialFibrations C₁)]
variable [HasFunctorialFactorization (trivialCofibrations C₁) (fibrations C₁)]
variable {I₁ : Type 1} (S₁ : I₁ → Arrow C₁)

example : MorphismProperty C₁ := localEquivalences S₁

end UniverseOneZero

section UniverseZero

variable {C₀ : Type} [Category C₀] [ModelCategory C₀]
variable [SimplicialCategory C₀]
variable [HasFunctorialFactorization (cofibrations C₀) (trivialFibrations C₀)]
variable [HasFunctorialFactorization (trivialCofibrations C₀) (fibrations C₀)]
variable {I₀ : Type} (S₀ : I₀ → Arrow C₀)

example : MorphismProperty C₀ := localEquivalences S₀

end UniverseZero

/- This leaf does not expose Smith recognition or a localized model structure. -/

/-- error: Unknown identifier `SmithRecognitionInput` -/
#guard_msgs (error) in
#check SmithRecognitionInput

/-- error: Unknown identifier `LeftBousfieldLocalizationData` -/
#guard_msgs (error) in
#check LeftBousfieldLocalizationData

/-- error: Unknown identifier `localizedFibrations` -/
#guard_msgs (error) in
#check localizedFibrations

end HomotopicalAlgebra.LeftBousfieldLocalizationLocalTests

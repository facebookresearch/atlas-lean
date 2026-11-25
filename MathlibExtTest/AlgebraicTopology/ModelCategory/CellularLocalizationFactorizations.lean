/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationFactorizations
import Batteries.Tactic.Lint

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w wS u v

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.CellularLocalizationFactorizations

section GenericOriginalClasses

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) {K : Type wS} (S : K → Arrow C)

example (k : K) : generatedLocalEquivalences d S (S k).hom := localizingMaps d S k

example : weakEquivalences C ≤ generatedLocalEquivalences d S := baseWeak_le d S

example : (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty := weak_twoOutOfThree d S

example : (generatedLocalEquivalences d S).IsStableUnderRetracts := weak_retracts d S

example : trivialCofibrations C ≤ localTrivialCofibrations d S := baseTrivialCofibrations_le d S

example : trivialFibrations C ≤ localFibrations d S := baseTrivialFibrations_le d S

example : localFibrations d S ≤ fibrations C := localFibrations_le_base d S

example {X Y : C} (f : X ⟶ Y)
    (hf : (localFibrations d S ⊓ generatedLocalEquivalences d S) f) :
    trivialFibrations C f := by
  rw [← trivialFibrations_eq d S]
  exact hf

example {X Y : C} (f : X ⟶ Y)
    (hf : (localFibrations d S ⊓ generatedLocalEquivalences d S) f) :
    RetractArrow f (d.cofibrantFactorizationData.factorizationData f).p :=
  trivialFibrationRetract d S f hf

example {X Y : C} (f : X ⟶ Y)
    (hf : (localFibrations d S ⊓ generatedLocalEquivalences d S) f) :
    (trivialFibrationRetract d S f hf).i.left ≫
        (d.cofibrantFactorizationData.factorizationData f).p =
      f ≫ (trivialFibrationRetract d S f hf).i.right :=
  (trivialFibrationRetract d S f hf).i_w

example {X Y : C} (f : X ⟶ Y)
    (hf : (localFibrations d S ⊓ generatedLocalEquivalences d S) f) :
    (trivialFibrationRetract d S f hf).i.right ≫
      (trivialFibrationRetract d S f hf).r.right = 𝟙 Y :=
  (trivialFibrationRetract d S f hf).retract_right

example {X Y : C} (f : X ⟶ Y)
    (hX : generatedLocalFibrant d S X) (hY : generatedLocalFibrant d S Y) :
    generatedLocalEquivalences d S f ↔ weakEquivalences C f := weak_iff_of_local d S f hX hY

example (A : C) {X Y : C} (g : X ⟶ Y) (hg : weakEquivalences C g) :
    IsIso (GeneratedRightMappingEnrichment.postcomp d A g) :=
  nativePostcomp_isIso_of_weak d A g hg

example {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) (hg : weakEquivalences C g) :
    IsIso (GeneratedRightMappingEnrichment.precomp d f X) ↔
      IsIso (GeneratedRightMappingEnrichment.precomp d f Y) :=
  nativePrecomp_target_iff d f g hg

example {X Y : C} (g : X ⟶ Y) (hg : weakEquivalences C g) :
    generatedIsDerivedLocal d S X ↔ generatedIsDerivedLocal d S Y :=
  derivedLocal_target_iff d S g hg

example {X Y : C} (g : X ⟶ Y) (hg : weakEquivalences C g)
    (hX : generatedLocalFibrant d S X) [IsFibrant Y] : generatedLocalFibrant d S Y :=
  localFibrant_of_weak d S g hg hX

end GenericOriginalClasses

#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.localizingMaps
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.baseWeak_le
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.nativePostcomp_isIso_of_weak
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.nativePrecomp_target_iff
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.derivedLocal_target_iff
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.localFibrant_of_weak
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.weak_containsIdentities
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.weak_twoOutOfThree
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.weak_retracts
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.baseTrivialCofibrations_le
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.baseTrivialFibrations_le
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.localFibrations_le_base
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.trivialFibrationRetract
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.trivialFibrations_eq
#print axioms HomotopicalAlgebra.CellularLocalizationFactorizations.weak_iff_of_local
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationFactorizations

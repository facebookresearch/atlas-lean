/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricStableSmashMonoidalModel

/-!
# Both original symmetric sphere-unit comparisons

The original native I factor at the initial sphere-unit arrow supplies the
same source and q for both complete comparison transformations. Their
components use the original left and right unitors. Sphere-unit cofibrancy,
the actual level pushout products and the same q prove both level weak
comparisons and their original Omega-target tests.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory CGWH.limits

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

private abbrev V := PointedCGWH.{u, v}
private abbrev Operator := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} Operator.{u, v}

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal monoidalCategory symmetricCategory monoidalClosed

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The sphere/free-zero comparison proves actual unit cofibrancy before recognition. -/
theorem levelTensorUnit_isCofibrant : IsCofibrant (𝟙_ Carrier.{u, v}) :=
  tensorUnit_isCofibrant (B := B)

/-- The source is the actual same-bottom I factor of the initial sphere-unit map. -/
def originalUnitReplacementSource : Carrier.{u, v} :=
  (originalLevelUnitFactor (B := B)).Z

/-- The same original I right factor is used in both comparison transformations. -/
def originalUnitReplacementMap : originalUnitReplacementSource.{u, v} (B := B) ⟶ 𝟙_ Carrier.{u, v} :=
  (originalLevelUnitFactor (B := B)).p

/-- The entire original middle functor is evaluated at the original initial sphere arrow. -/
theorem originalUnitReplacementSource_eq :
    originalUnitReplacementSource.{u, v} (B := B) =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := Operator.{u, v}) (B := B)).Z.obj
          (CategoryTheory.Arrow.mk (initial.to (𝟙_ Carrier.{u, v}))) := rfl

/-- This q is the original right-factor transformation at that same Arrow. -/
theorem originalUnitReplacementMap_eq :
    originalUnitReplacementMap.{u, v} (B := B) =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := Operator.{u, v}) (B := B)).p.app
          (CategoryTheory.Arrow.mk (initial.to (𝟙_ Carrier.{u, v}))) := rfl

/-- Both original factor legs retain the actual initial-unit factor equation. -/
theorem originalUnitReplacement_fac :
    (originalLevelUnitFactor (B := B)).i ≫ originalUnitReplacementMap.{u, v} (B := B) =
      initial.to (𝟙_ Carrier.{u, v}) :=
  (originalLevelUnitFactor (B := B)).fac

/-- The original I source is cofibrant in the original native level model. -/
theorem originalUnitReplacementSource_isCofibrant :
    IsCofibrant (originalUnitReplacementSource.{u, v} (B := B)) :=
  (levelUnitAxiomWitness (B := B)).Q_cofibrant

/-- The same q is an actual original level trivial fibration. -/
theorem originalUnitReplacementMap_trivialFibration :
    trivialFibrations Carrier.{u, v} (originalUnitReplacementMap.{u, v} (B := B)) :=
  (originalLevelUnitFactor (B := B)).hp

/-- The whole left comparison retains q and the actual left-unitor family. -/
def originalLeftUnitComparison :
    tensorLeft (originalUnitReplacementSource.{u, v} (B := B)) ⟶ 𝟭 Carrier.{u, v} :=
  leftUnitReplacementMap (originalUnitReplacementMap.{u, v} (B := B))

/-- The whole right comparison retains the same q and actual right-unitor family. -/
def originalRightUnitComparison :
    tensorRight (originalUnitReplacementSource.{u, v} (B := B)) ⟶ 𝟭 Carrier.{u, v} :=
  rightUnitReplacementMap (originalUnitReplacementMap.{u, v} (B := B))

/-- The actual left component is the original q tensored with X, then its original unitor. -/
theorem originalLeftUnitComparison_app (X : Carrier.{u, v}) :
    (originalLeftUnitComparison.{u, v} (B := B)).app X =
      (originalUnitReplacementMap.{u, v} (B := B) ▷ X) ≫ (λ_ X).hom := rfl

/-- The actual right component uses X tensored with the same original q, then its unitor. -/
theorem originalRightUnitComparison_app (X : Carrier.{u, v}) :
    (originalRightUnitComparison.{u, v} (B := B)).app X =
      (X ◁ originalUnitReplacementMap.{u, v} (B := B)) ≫ (ρ_ X).hom := rfl

/-- Every original input arrow retains the complete left comparison square. -/
theorem originalLeftUnitComparison_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (originalUnitReplacementSource.{u, v} (B := B) ◁ f) ≫
        (originalLeftUnitComparison.{u, v} (B := B)).app Y =
      (originalLeftUnitComparison.{u, v} (B := B)).app X ≫ f :=
  (originalLeftUnitComparison.{u, v} (B := B)).naturality f

/-- Every original input arrow retains the complete right comparison square. -/
theorem originalRightUnitComparison_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (f ▷ originalUnitReplacementSource.{u, v} (B := B)) ≫
        (originalRightUnitComparison.{u, v} (B := B)).app Y =
      (originalRightUnitComparison.{u, v} (B := B)).app X ≫ f :=
  (originalRightUnitComparison.{u, v} (B := B)).naturality f

/-- The entire left natural transformation is the one in the original unit witness. -/
theorem originalLeftUnitComparison_eq_levelWitness :
    originalLeftUnitComparison.{u, v} (B := B) =
      leftUnitReplacementMap (levelUnitAxiomWitness (B := B)).q := rfl

/-- The entire right natural transformation is the one in the same original witness. -/
theorem originalRightUnitComparison_eq_levelWitness :
    originalRightUnitComparison.{u, v} (B := B) =
      rightUnitReplacementMap (levelUnitAxiomWitness (B := B)).q := rfl

/-- Actual level pushout products and independent sphere cofibrancy prove the left comparison. -/
theorem originalLeftUnitComparison_weak (X : Carrier.{u, v}) [IsCofibrant X] :
    weakEquivalences Carrier.{u, v} ((originalLeftUnitComparison.{u, v} (B := B)).app X) :=
  levelUnitReplacement_left X

/-- The same original factor and actual right unitor prove the right level comparison. -/
theorem originalRightUnitComparison_weak (X : Carrier.{u, v}) [IsCofibrant X] :
    weakEquivalences Carrier.{u, v} ((originalRightUnitComparison.{u, v} (B := B)).app X) :=
  levelUnitReplacement_right X

/-- The entire original left component passes every original Omega-target Hom test. -/
theorem originalLeftUnitComparison_omegaTests (X : Carrier.{u, v}) [IsCofibrant X] :
    NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((((HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
          (A := Operator.{u, v}) (B := B)).p.app
            (Arrow.mk (initial.to (𝟙_ Carrier.{u, v})))) ▷ X) ≫ (λ_ X).hom) := by
  have h := NativeK.levelWeak_le_omegaTests Actual.symmetricFamily.{u, v} _
    (originalLeftUnitComparison_weak.{u, v} X)
  rw [originalLeftUnitComparison_app] at h
  rw [originalUnitReplacementMap_eq] at h
  exact h

/-- The entire original right component passes the same original Omega-target tests. -/
theorem originalRightUnitComparison_omegaTests (X : Carrier.{u, v}) [IsCofibrant X] :
    NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((X ◁ ((HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
          (A := Operator.{u, v}) (B := B)).p.app
            (Arrow.mk (initial.to (𝟙_ Carrier.{u, v}))))) ≫ (ρ_ X).hom) := by
  have h := NativeK.levelWeak_le_omegaTests Actual.symmetricFamily.{u, v} _
    (originalRightUnitComparison_weak.{u, v} X)
  rw [originalRightUnitComparison_app] at h
  rw [originalUnitReplacementMap_eq] at h
  exact h

/-!
## The literal original native Q unit counit
-/

/-- Keep the literal original Q object as constructor data before the source,
counit and both complete comparison transformations are declared. -/
private abbrev originalNativeUnitSourceData : Carrier.{u, v} :=
  (Replacement.cofibrantReplacement (A := Operator.{u, v}) (B := B)).obj (𝟙_ Carrier.{u, v})

/-- This unit source is the original native replacement at the sphere unit. -/
def nativeUnitReplacementSource : Carrier.{u, v} :=
  (Replacement.cofibrantReplacement (A := Operator.{u, v}) (B := B)).obj (𝟙_ Carrier.{u, v})

/-- The source data is the complete original Q object at the sphere unit. -/
private theorem nativeUnitReplacementSource_original_data :
    nativeUnitReplacementSource.{u, v} (B := B) =
      originalNativeUnitSourceData.{u, v} (B := B) := rfl

/-- This q is the entire original replacement counit evaluated at the actual sphere unit. -/
def nativeUnitReplacementMap : originalNativeUnitSourceData.{u, v} (B := B) ⟶ 𝟙_ Carrier.{u, v} :=
  (Replacement.cofibrantReplacementCounit (A := Operator.{u, v}) (B := B)).app
    (𝟙_ Carrier.{u, v})

/-- The original native zero-arrow input and whole I middle functor are retained. -/
theorem nativeUnitReplacementSource_eq :
    nativeUnitReplacementSource.{u, v} (B := B) =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := Operator.{u, v}) (B := B)).Z.obj
          (Diagrams.fromZeroArrow.obj (𝟙_ Carrier.{u, v})) := rfl

/-- The native q retains the original right factor at the same original zero-arrow input. -/
theorem nativeUnitReplacementMap_eq :
    nativeUnitReplacementMap.{u, v} (B := B) =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := Operator.{u, v}) (B := B)).p.app
          (Diagrams.fromZeroArrow.obj (𝟙_ Carrier.{u, v})) := rfl

/-- The entire original native Q source is cofibrant in the actual original level model. -/
theorem nativeUnitReplacementSource_isCofibrant :
    IsCofibrant (nativeUnitReplacementSource.{u, v} (B := B)) := by
  change IsCofibrant
    ((Replacement.cofibrantReplacement (A := Operator.{u, v}) (B := B)).obj (𝟙_ Carrier.{u, v}))
  exact Replacement.isCofibrant_cofibrantReplacement
    (A := Operator.{u, v}) (B := B) (𝟙_ Carrier.{u, v})

/-- Its exact original Q counit is an actual original level trivial fibration. -/
theorem nativeUnitReplacementMap_trivialFibration :
    trivialFibrations Carrier.{u, v} (nativeUnitReplacementMap.{u, v} (B := B)) :=
  Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B) (𝟙_ Carrier.{u, v})

/-- Both actual original native I replacement legs retain their zero-arrow equation. -/
theorem nativeUnitReplacement_fac :
    (Replacement.initialToCofibrantReplacement (A := Operator.{u, v}) (B := B)).app
        (𝟙_ Carrier.{u, v}) ≫ nativeUnitReplacementMap.{u, v} (B := B) =
      Diagrams.zeroTo (𝟙_ Carrier.{u, v}) :=
  (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
    (A := Operator.{u, v}) (B := B)).fac_app

/-- The complete left transformation uses the literal native Q unit counit. -/
def nativeLeftUnitComparison :
    tensorLeft (originalNativeUnitSourceData.{u, v} (B := B)) ⟶ 𝟭 Carrier.{u, v} :=
  leftUnitReplacementMap (nativeUnitReplacementMap.{u, v} (B := B))

/-- The complete right transformation uses the same literal native Q unit counit. -/
def nativeRightUnitComparison :
    tensorRight (originalNativeUnitSourceData.{u, v} (B := B)) ⟶ 𝟭 Carrier.{u, v} :=
  rightUnitReplacementMap (nativeUnitReplacementMap.{u, v} (B := B))

/-- The full original left comparison retains all of its original object and arrow values. -/
private theorem nativeLeftUnitComparison_original_data :
    nativeLeftUnitComparison.{u, v} (B := B) =
      leftUnitReplacementMap (nativeUnitReplacementMap.{u, v} (B := B)) := rfl

/-- The full original right comparison retains the same q and every original arrow value. -/
private theorem nativeRightUnitComparison_original_data :
    nativeRightUnitComparison.{u, v} (B := B) =
      rightUnitReplacementMap (nativeUnitReplacementMap.{u, v} (B := B)) := rfl

/-- Every actual left component retains the original native q and its actual left unitor. -/
theorem nativeLeftUnitComparison_app (X : Carrier.{u, v}) :
    (nativeLeftUnitComparison.{u, v} (B := B)).app X =
      (nativeUnitReplacementMap.{u, v} (B := B) ▷ X) ≫ (λ_ X).hom := rfl

/-- Every actual right component retains the same native q and its actual right unitor. -/
theorem nativeRightUnitComparison_app (X : Carrier.{u, v}) :
    (nativeRightUnitComparison.{u, v} (B := B)).app X =
      (X ◁ nativeUnitReplacementMap.{u, v} (B := B)) ≫ (ρ_ X).hom := rfl

/-- The full original left native-Q comparison retains every input-arrow square. -/
theorem nativeLeftUnitComparison_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (originalNativeUnitSourceData.{u, v} (B := B) ◁ f) ≫
        (nativeLeftUnitComparison.{u, v} (B := B)).app Y =
      (nativeLeftUnitComparison.{u, v} (B := B)).app X ≫ f :=
  (nativeLeftUnitComparison.{u, v} (B := B)).naturality f

/-- The full original right native-Q comparison retains every input-arrow square. -/
theorem nativeRightUnitComparison_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (f ▷ originalNativeUnitSourceData.{u, v} (B := B)) ≫
        (nativeRightUnitComparison.{u, v} (B := B)).app Y =
      (nativeRightUnitComparison.{u, v} (B := B)).app X ≫ f :=
  (nativeRightUnitComparison.{u, v} (B := B)).naturality f

/-- Actual level PP and independent sphere cofibrancy verify the literal native left comparison. -/
theorem nativeLeftUnitComparison_weak (X : Carrier.{u, v}) [IsCofibrant X] :
    weakEquivalences Carrier.{u, v} ((nativeLeftUnitComparison.{u, v} (B := B)).app X) := by
  let _ : IsCofibrant (𝟙_ Carrier.{u, v}) := levelTensorUnit_isCofibrant.{u, v} (B := B)
  let P : MonoidalPushoutProductAxiom Carrier.{u, v} := levelPushoutProductAxiom (B := B)
  let Q : Carrier.{u, v} := originalNativeUnitSourceData.{u, v} (B := B)
  let q : Q ⟶ 𝟙_ Carrier.{u, v} := nativeUnitReplacementMap.{u, v} (B := B)
  have hQ : IsCofibrant Q := nativeUnitReplacementSource_isCofibrant.{u, v} (B := B)
  have hq : trivialFibrations Carrier.{u, v} q :=
    nativeUnitReplacementMap_trivialFibration.{u, v} (B := B)
  exact P.leftUnitReplacementMap_weak q hQ hq X

/-- The same original native Q counit and actual right unitor give the right level comparison. -/
theorem nativeRightUnitComparison_weak (X : Carrier.{u, v}) [IsCofibrant X] :
    weakEquivalences Carrier.{u, v} ((nativeRightUnitComparison.{u, v} (B := B)).app X) := by
  let _ : IsCofibrant (𝟙_ Carrier.{u, v}) := levelTensorUnit_isCofibrant.{u, v} (B := B)
  let P : MonoidalPushoutProductAxiom Carrier.{u, v} := levelPushoutProductAxiom (B := B)
  let Q : Carrier.{u, v} := originalNativeUnitSourceData.{u, v} (B := B)
  let q : Q ⟶ 𝟙_ Carrier.{u, v} := nativeUnitReplacementMap.{u, v} (B := B)
  have hQ : IsCofibrant Q := nativeUnitReplacementSource_isCofibrant.{u, v} (B := B)
  have hq : trivialFibrations Carrier.{u, v} q :=
    nativeUnitReplacementMap_trivialFibration.{u, v} (B := B)
  exact P.rightUnitReplacementMap_weak q hQ hq X

/-- The literal native left q/unitor comparison passes every actual original Omega test. -/
theorem nativeLeftUnitComparison_omegaTests (X : Carrier.{u, v}) [IsCofibrant X] :
    NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((((Replacement.cofibrantReplacementCounit (A := Operator.{u, v}) (B := B)).app
          (𝟙_ Carrier.{u, v})) ▷ X) ≫ (λ_ X).hom) := by
  have h := NativeK.levelWeak_le_omegaTests Actual.symmetricFamily.{u, v} _
    (nativeLeftUnitComparison_weak.{u, v} X)
  rw [nativeLeftUnitComparison_app] at h
  exact h

/-- The literal native right q/unitor comparison passes the same actual original Omega tests. -/
theorem nativeRightUnitComparison_omegaTests (X : Carrier.{u, v}) [IsCofibrant X] :
    NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((X ◁ ((Replacement.cofibrantReplacementCounit (A := Operator.{u, v}) (B := B)).app
          (𝟙_ Carrier.{u, v}))) ≫ (ρ_ X).hom) := by
  have h := NativeK.levelWeak_le_omegaTests Actual.symmetricFamily.{u, v} _
    (nativeRightUnitComparison_weak.{u, v} X)
  rw [nativeRightUnitComparison_app] at h
  exact h

/-- The actual level unit witness uses the original native Q object and exact counit. -/
def nativeLevelUnitAxiomWitness : MonoidalUnitAxiomWitness Carrier.{u, v} := by
  let _ : IsCofibrant (𝟙_ Carrier.{u, v}) := levelTensorUnit_isCofibrant.{u, v} (B := B)
  exact (levelPushoutProductAxiom (B := B)).unitAxiomWitnessOfCofibrantUnit
    (nativeUnitReplacementMap.{u, v} (B := B)) (nativeUnitReplacementSource_isCofibrant.{u, v} (B := B))
    (nativeUnitReplacementMap_trivialFibration.{u, v} (B := B))

/-- Both computational fields of the level witness retain the exact original native values. -/
theorem nativeLevelUnitAxiomWitness_original_fields :
    (nativeLevelUnitAxiomWitness.{u, v} (B := B)).Q = nativeUnitReplacementSource.{u, v} (B := B) ∧
      (nativeLevelUnitAxiomWitness.{u, v} (B := B)).q = nativeUnitReplacementMap.{u, v} (B := B) :=
  ⟨rfl, rfl⟩

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

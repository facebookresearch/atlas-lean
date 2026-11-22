/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalRecognition
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.OriginalFactors

/-!
# Conditional model assembly on the full native orthogonal carrier

The exact original comparison premise remains an explicit argument.
Conditional recognition and the unchanged original I/K algorithms build
one actual model value on the original continuous enriched carrier.
Its five morphism classes, two WFS, entire generator families and native
Omega fibrancy are identified with the same original source definitions.

These conditional helpers give no unconditional final stable model.
Neither a desired model nor a localization or replacement outcome is
an input. Generation uses the original realized cardinal and does not
assert combinatoriality of pointed CGWH or of its spectrum carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalModel

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
  NativeK.generators_isCardinalForSmallObjectArgument

private instance finiteLimits : HasFiniteLimits C.{u, v} :=
  (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (B := B) (A := O)).cm1a

private instance finiteColimits : HasFiniteColimits C.{u, v} :=
  (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (B := B) (A := O)).cm1b

/-- The same entire original records supply conditional recognition,
with class laws proved from the actual original comparison premise. -/
def recognitionData (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    OriginalGeneratedModel.RecognitionData originalI stableWeakEquivalences :=
  OriginalGeneratedModel.recognition originalI originalK stableWeakEquivalences inferInstance
    (ConditionalRecognition.right_class_eq hComparison)
    originalKLeft_le_stableWeakEquivalences originalIFactorizationData originalKFactorizationData

/-- The entire correlated generator family and both original records
are the literal original values in the recognition record. -/
theorem recognition_original_fields (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    (recognitionData hComparison).J = originalK ∧
      (recognitionData hComparison).givenI = originalIFactorizationData ∧
      (recognitionData hComparison).givenK = originalKFactorizationData := ⟨rfl, rfl, rfl⟩

/-- The exact original I WFS is interpreted in the full stable intersections. -/
theorem conditional_I_wfs (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    IsWeakFactorizationSystem stableCofibrations.{u, v} stableTrivialFibrations := by
  rw [← ConditionalRecognition.right_class_eq hComparison]
  exact originalI_wfs

/-- The same original paired K WFS is interpreted in those full intersections. -/
theorem conditional_K_wfs (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    IsWeakFactorizationSystem stableTrivialCofibrations.{u, v} stableFibrations := by
  rw [← ConditionalRecognition.left_class_eq hComparison]
  exact originalK_wfs

/-- A conditional actual model value on the unchanged native carrier,
constructed from the same original I/K records and source recognition. -/
@[instance_reducible]
def modelCategory (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    ModelCategory C.{u, v} :=
  OriginalGeneratedModel.modelCategory originalI originalK stableWeakEquivalences inferInstance
    (ConditionalRecognition.right_class_eq hComparison)
    originalKLeft_le_stableWeakEquivalences originalIFactorizationData originalKFactorizationData

/-- All five classes belong to this same conditional actual model value. -/
theorem five_classes (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    weakEquivalences C.{u, v} = stableWeakEquivalences ∧
      cofibrations C.{u, v} = stableCofibrations ∧
      fibrations C.{u, v} = stableFibrations ∧
      trivialCofibrations C.{u, v} = originalK.rlp.llp ∧
      trivialFibrations C.{u, v} = originalI.rlp :=
  OriginalGeneratedModel.five_classes originalI originalK stableWeakEquivalences inferInstance
    (ConditionalRecognition.right_class_eq hComparison)
    originalKLeft_le_stableWeakEquivalences originalIFactorizationData originalKFactorizationData

/-- The weak class of this model is exactly every original native Omega Ho test. -/
theorem weakEquivalences_eq (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    weakEquivalences C.{u, v} = stableWeakEquivalences := (five_classes hComparison).1

/-- Its cofibrations are exactly the unchanged original I-left class. -/
theorem cofibrations_eq (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    cofibrations C.{u, v} = stableCofibrations := (five_classes hComparison).2.1

/-- Its fibrations are exactly the entire original correlated K-right class. -/
theorem fibrations_eq (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    fibrations C.{u, v} = stableFibrations := (five_classes hComparison).2.2.1

/-- Recognition identifies its entire trivial-left class with original K-left. -/
theorem trivialCofibrations_eq (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    trivialCofibrations C.{u, v} = originalK.rlp.llp := (five_classes hComparison).2.2.2.1

/-- Recognition identifies its entire trivial-right class with original I-right. -/
theorem trivialFibrations_eq (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    trivialFibrations C.{u, v} = originalI.rlp := (five_classes hComparison).2.2.2.2

/-- The conditional model and original native level model have the
same actual ordinary cofibration property on the same enriched maps. -/
theorem cofibrations_eq_level (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    (modelCategory hComparison).categoryWithCofibrations.cofibrations =
      (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
        (B := B) (A := O)).categoryWithCofibrations.cofibrations :=
  stableCofibrations_eq_level

/-- Ordinary cofibrations retain the entire original I cell closure,
its realized-generator ordinal and the caller's same ordinal bottom. -/
theorem cofibrations_eq_retractCells (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    cofibrations C.{u, v} =
      ((coproducts.{v} originalI).pushouts.transfiniteCompositionsOfShape
        realizedGeneratorCardinal.{v}.ord.ToType).retracts :=
  (cofibrations_eq hComparison).trans stableCofibrations_eq_retractCells

/-- Trivial cofibrations retain the full original paired K cell closure
with precisely the same original cardinal shape. -/
theorem trivialCofibrations_eq_retractCells
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    trivialCofibrations C.{u, v} =
      ((coproducts.{v} originalK).pushouts.transfiniteCompositionsOfShape
        realizedGeneratorCardinal.{v}.ord.ToType).retracts :=
  (trivialCofibrations_eq hComparison).trans originalKLeft_eq_retractCells

/-- All original paired native mapping corners, at every source and
added degree, remain the actual conditional fibration criterion. -/
theorem fibration_iff_fullCorners (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (p : X ⟶ Y) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    fibrations C.{u, v} p ↔
      (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
        (B := B) (A := O)).categoryWithFibrations.fibrations p ∧
      ∀ l : ℕ × ℕ, trivialFibrations PointedCGWH.{u, v}
        (PointedCGWH.NativeMappingCorner.square
          (NativeK.cylinderSource orthogonalFamily l) p).π := by
  let : ModelCategory C.{u, v} := modelCategory hComparison
  change stableFibrations p ↔
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
      (B := B) (A := O)).categoryWithFibrations.fibrations p ∧
    ∀ l : ℕ × ℕ, trivialFibrations PointedCGWH.{u, v}
      (PointedCGWH.NativeMappingCorner.square (NativeK.cylinderSource orthogonalFamily l) p).π
  exact stableFibrations_iff p

/-- Fibrant objects are exactly the original full-family native Omega objects. -/
theorem isFibrant_iff_isOmega (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    IsFibrant X ↔ NativeK.IsOmega orthogonalFamily X := by
  let : ModelCategory C.{u, v} := modelCategory hComparison
  change IsFibrant X ↔ NativeK.IsOmega orthogonalFamily X
  rw [isFibrant_iff_of_isTerminal (Diagrams.toZero X) Diagrams.zeroDiagramIsTerminal,
    HomotopicalAlgebra.fibration_iff]
  change stableFibrations (Diagrams.toZero X) ↔ NativeK.IsOmega orthogonalFamily X
  exact NativeK.lifting_toZero_iff_isOmega orthogonalFamily X

/-- Both complete original families provide cofibrant generation at
the original realized cardinal, without a combinatoriality assertion. -/
def generationData (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    CofibrantGenerationData C.{u, v} realizedGeneratorCardinal.{v} := by
  let : ModelCategory C.{u, v} := modelCategory hComparison
  exact
    { I := originalI
      J := originalK
      I_smallObject :=
        HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
      J_smallObject := NativeK.generators_isCardinalForSmallObjectArgument orthogonalFamily
      I_rlp := (trivialFibrations_eq hComparison).symm
      J_rlp := (fibrations_eq hComparison).symm }

/-- The complete generator records remain the same original I and K properties. -/
theorem generationData_original_families
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    (generationData hComparison).I = originalI ∧
      (generationData hComparison).J = originalK := ⟨rfl, rfl⟩

/-- Both model WFS use the same actual classes and the unchanged original algorithms. -/
theorem model_wfs (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelCategory hComparison
    IsWeakFactorizationSystem (cofibrations C.{u, v}) (trivialFibrations C.{u, v}) ∧
      IsWeakFactorizationSystem (trivialCofibrations C.{u, v}) (fibrations C.{u, v}) := by
  let : ModelCategory C.{u, v} := modelCategory hComparison
  change IsWeakFactorizationSystem stableCofibrations stableTrivialFibrations ∧
    IsWeakFactorizationSystem stableTrivialCofibrations stableFibrations
  exact ⟨conditional_I_wfs hComparison, conditional_K_wfs hComparison⟩

/-- The conditional actual model value is independent of the proof term
of the same exact original comparison proposition. -/
theorem modelCategory_proof_irrel (h h' : ComparisonHomBijections.{u, v} (B := B)) :
    modelCategory h = modelCategory h' := rfl

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalModel

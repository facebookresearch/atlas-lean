/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalReplacements
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalQuillen

/-!
# Explicit conditional original orthogonal defaults and record contexts

The named conditional values use the actual native carrier and the
unchanged original I/K algorithms, entire Q/R functors and all four
replacement maps. They have only the exact original comparison Hom
premise as a mathematical input. No global stable model is installed.

The model record carrier also receives those same entire given factors
through the original identity maps. Every middle object, native Arrow
action, factor leg and equation retains the original value. These are
explicit given records; no equality with an existentially selected
factorization getter is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalDefaults

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev C := OrthogonalCarrier.{u, v}
private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The named conditional model has the original full native spectrum carrier. -/
abbrev modelOfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    ModelCategory C.{u, v} := ConditionalModel.modelCategory hComparison

/-- Its named generation data retain both full original families and their original cardinal. -/
def generationOfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelOfComparison hComparison
    CofibrantGenerationData C.{u, v} realizedGeneratorCardinal.{v} :=
  ConditionalModel.generationData hComparison

/-- The named native I record is the same entire original classified algorithm. -/
def IFactorOfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelOfComparison hComparison
    FunctorialFactorizationData (cofibrations C.{u, v}) (trivialFibrations C.{u, v}) :=
  ConditionalFactorizations.IFactorizationData hComparison

/-- The named native paired K record is the same whole original classified algorithm. -/
def KFactorOfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelOfComparison hComparison
    FunctorialFactorizationData (trivialCofibrations C.{u, v}) (fibrations C.{u, v}) :=
  ConditionalFactorizations.KFactorizationData hComparison

/-- The named Q value is the complete original I replacement function. -/
def QOfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) : C.{u, v} ⥤ C.{u, v} :=
  ConditionalReplacements.QFunctor hComparison

/-- Its named counit retains every entire original projection component. -/
def QCounitOfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    QOfComparison hComparison ⟶ 𝟭 C.{u, v} := ConditionalReplacements.qCounit hComparison

/-- Its named initial leg is the complete original zero-source I injection. -/
def initialToQOfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    (Functor.const C.{u, v}).obj Diagrams.zeroDiagram ⟶ QOfComparison hComparison :=
  ConditionalReplacements.initialToQ hComparison

/-- The named R value is the complete original paired K Omega replacement function. -/
def ROfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) : C.{u, v} ⥤ C.{u, v} :=
  ConditionalReplacements.RFunctor hComparison

/-- Its named unit retains every actual original replacement source. -/
def RUnitOfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    𝟭 C.{u, v} ⟶ ROfComparison hComparison := ConditionalReplacements.rUnit hComparison

/-- Its named projection is the complete original paired K zero-target map. -/
def RToZeroOfComparison (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    ROfComparison hComparison ⟶ (Functor.const C.{u, v}).obj Diagrams.zeroDiagram :=
  ConditionalReplacements.rToZero hComparison

/-- Every full factor field in the named native defaults is its original source value. -/
theorem original_factor_defaults (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    (IFactorOfComparison hComparison).Z = originalIFactorizationData.Z ∧
      (IFactorOfComparison hComparison).i = originalIFactorizationData.i ∧
      (IFactorOfComparison hComparison).p = originalIFactorizationData.p ∧
      (KFactorOfComparison hComparison).Z = originalKFactorizationData.Z ∧
      (KFactorOfComparison hComparison).i = originalKFactorizationData.i ∧
      (KFactorOfComparison hComparison).p = originalKFactorizationData.p :=
  ConditionalFactorizations.original_fields hComparison

/-- Both whole replacement defaults and all four complete maps keep
the same original native carrier, functions and source choices. -/
theorem original_replacement_defaults (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    QOfComparison hComparison = Replacement.cofibrantReplacement (B := B) (A := O) ∧
      initialToQOfComparison hComparison =
        Replacement.initialToCofibrantReplacement (B := B) (A := O) ∧
      QCounitOfComparison hComparison = Replacement.cofibrantReplacementCounit (B := B) (A := O) ∧
      ROfComparison hComparison = NativeK.omegaReplacement orthogonalFamily ∧
      RUnitOfComparison hComparison = NativeK.omegaReplacementUnit orthogonalFamily ∧
      RToZeroOfComparison hComparison = Functor.whiskerLeft Diagrams.toZeroArrow
        (NativeK.factorizationData orthogonalFamily).p :=
  ConditionalReplacements.replacement_original_fields hComparison

/-- The named generation defaults retain the entire actual original I and paired K families. -/
theorem original_generation_defaults (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelOfComparison hComparison
    (generationOfComparison hComparison).I = originalI ∧
      (generationOfComparison hComparison).J = originalK := ⟨rfl, rfl⟩

/-- All five default classes belong to this one conditional actual native model. -/
theorem five_default_classes (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    let : ModelCategory C.{u, v} := modelOfComparison hComparison
    weakEquivalences C.{u, v} = stableWeakEquivalences ∧
      cofibrations C.{u, v} = stableCofibrations ∧
      fibrations C.{u, v} = stableFibrations ∧
      trivialCofibrations C.{u, v} = originalK.rlp.llp ∧
      trivialFibrations C.{u, v} = originalI.rlp := ConditionalModel.five_classes hComparison

/-- The named defaults use exactly the full original Omega fibrancy condition. -/
theorem default_isFibrant_iff_isOmega (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (X : C.{u, v}) :
    let : ModelCategory C.{u, v} := modelOfComparison hComparison
    IsFibrant X ↔ NativeK.IsOmega orthogonalFamily X :=
  ConditionalModel.isFibrant_iff_isOmega hComparison X

/-- The two model record contexts of the named defaults have the
actual original identity Quillen adjunction. -/
theorem default_identity_isQuillen (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    (ConditionalQuillen.adjunction hComparison).IsQuillenAdjunction :=
  ConditionalQuillen.isQuillen hComparison

/-- The entire original I record is transported through the same
native identity into its own actual model record context. -/
def IFactorOnCarrier (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    FunctorialFactorizationData
      (cofibrations (ConditionalQuillen.StableCarrier hComparison))
      (trivialFibrations (ConditionalQuillen.StableCarrier hComparison)) :=
  OriginalGeneratedModel.cofibrantFactorizationOnCarrier
    originalI originalK stableWeakEquivalences inferInstance
    (ConditionalRecognition.right_class_eq hComparison)
    originalKLeft_le_stableWeakEquivalences originalIFactorizationData originalKFactorizationData

/-- The same entire original paired K record is transported through
the same two identity functions, with its original class membership. -/
def KFactorOnCarrier (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    FunctorialFactorizationData
      (trivialCofibrations (ConditionalQuillen.StableCarrier hComparison))
      (fibrations (ConditionalQuillen.StableCarrier hComparison)) :=
  OriginalGeneratedModel.fibrantFactorizationOnCarrier
    originalI originalK stableWeakEquivalences inferInstance
    (ConditionalRecognition.right_class_eq hComparison)
    originalKLeft_le_stableWeakEquivalences originalIFactorizationData originalKFactorizationData

/-- Both whole transported middle functors are the original full
native I/K functions between the unchanged identity comparisons. -/
theorem carrier_original_middle (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    (IFactorOnCarrier hComparison).Z =
        (ExplicitModelIdentity.toBase (modelOfComparison hComparison)).mapArrow ⋙
          originalIFactorizationData.Z ⋙
            ExplicitModelIdentity.ofBase (modelOfComparison hComparison) ∧
      (KFactorOnCarrier hComparison).Z =
        (ExplicitModelIdentity.toBase (modelOfComparison hComparison)).mapArrow ⋙
          originalKFactorizationData.Z ⋙
            ExplicitModelIdentity.ofBase (modelOfComparison hComparison) :=
  ⟨rfl, rfl⟩

/-- Every full original input square retains the actual entire native
I/K middle maps after forgetting the two model record contexts. -/
theorem carrier_original_maps (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {F G : Arrow (ConditionalQuillen.StableCarrier hComparison)} (f : F ⟶ G) :
    ((IFactorOnCarrier hComparison).Z.map f).hom =
        originalIFactorizationData.Z.map
          ((ExplicitModelIdentity.toBase (modelOfComparison hComparison)).mapArrow.map f) ∧
      ((KFactorOnCarrier hComparison).Z.map f).hom =
        originalKFactorizationData.Z.map
          ((ExplicitModelIdentity.toBase (modelOfComparison hComparison)).mapArrow.map f) :=
  ⟨rfl, rfl⟩

/-- All four transported factor legs retain the original full native
injection and projection functions on the same actual source Arrow. -/
theorem carrier_original_legs (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (F : Arrow (ConditionalQuillen.StableCarrier hComparison)) :
    ((IFactorOnCarrier hComparison).i.app F).hom = originalIFactorizationData.i.app
        ((ExplicitModelIdentity.toBase (modelOfComparison hComparison)).mapArrow.obj F) ∧
      ((IFactorOnCarrier hComparison).p.app F).hom = originalIFactorizationData.p.app
        ((ExplicitModelIdentity.toBase (modelOfComparison hComparison)).mapArrow.obj F) ∧
      ((KFactorOnCarrier hComparison).i.app F).hom = originalKFactorizationData.i.app
        ((ExplicitModelIdentity.toBase (modelOfComparison hComparison)).mapArrow.obj F) ∧
      ((KFactorOnCarrier hComparison).p.app F).hom = originalKFactorizationData.p.app
        ((ExplicitModelIdentity.toBase (modelOfComparison hComparison)).mapArrow.obj F) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Both entire original records factor every unchanged full input
Arrow in its model record context. -/
theorem carrier_factorization_fac (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (F : Arrow (ConditionalQuillen.StableCarrier hComparison)) :
    (IFactorOnCarrier hComparison).i.app F ≫ (IFactorOnCarrier hComparison).p.app F = F.hom ∧
      (KFactorOnCarrier hComparison).i.app F ≫ (KFactorOnCarrier hComparison).p.app F = F.hom :=
  ⟨(IFactorOnCarrier hComparison).fac_app, (KFactorOnCarrier hComparison).fac_app⟩

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalDefaults

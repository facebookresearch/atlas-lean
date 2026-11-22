/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.GenericOriginalLevelModel
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.CanonicalGenerationData
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableModels
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.CanonicalStableModelConsumers
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialStableModelProperties
public import MathlibExt.AlgebraicTopology.Spectra.IndexOperators.NativeStableAdjunctions
public import MathlibExt.AlgebraicTopology.Spectra.IndexOperators.NativeFibrantReflection

/-!
# Sequential spectrum model APIs

Sequential level models retain their generating cardinal and source conditions.
The native stable model determines its five classes, original I/K factorizations,
cofibrant and fibrant replacements, and integer homotopy criterion. The original
spectrum index adjunctions are Quillen for the constructed stable models, and
derived restrictions preserve and reflect their stable weak classes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed ZeroObject

namespace MathlibExtTest.AlgebraicTopology.Spectra.SequentialModelAPI

section GenericLevel

universe w uV vV

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [ModelCategory V] [IsClosedSymmetricMonoidalModelCategory V]
  [HasColimitsOfSize.{w, w} V] [LocallySmall.{w} V]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (T : V) [IsCofibrant T] (d : CofibrantGenerationData V κ)
  (hSourceI : GenericSequentialLevel.SourceCondition (κ := κ) T d.I)
  (hSourceJ : GenericSequentialLevel.SourceCondition (κ := κ) T d.J)

local instance smallColimits : HasColimitsOfSize.{0, 0} V :=
  hasColimitsOfSizeShrink.{0, 0, w, w} V

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

private def selectedGenericLevelModel : ModelCategory (SequentialSpectrum V T) :=
  GenericSequentialLevel.originalModelCategory T d hSourceI hSourceJ

local instance : ModelCategory (SequentialSpectrum V T) :=
  selectedGenericLevelModel T d hSourceI hSourceJ

example : weakEquivalences (SequentialSpectrum V T) =
    GenericSequentialLevel.originalLevelProperty T (weakEquivalences V) :=
  GenericSequentialLevel.original_weakEquivalences_eq T d hSourceI hSourceJ

example : fibrations (SequentialSpectrum V T) =
    GenericSequentialLevel.originalLevelProperty T (fibrations V) :=
  GenericSequentialLevel.original_fibrations_eq T d hSourceI hSourceJ

example : trivialFibrations (SequentialSpectrum V T) =
    GenericSequentialLevel.originalLevelProperty T (trivialFibrations V) :=
  GenericSequentialLevel.original_trivialFibrations_eq T d hSourceI hSourceJ

example : cofibrations (SequentialSpectrum V T) =
    (GenericSequentialLevel.originalGenerators T d.I).rlp.llp :=
  GenericSequentialLevel.original_cofibrations_eq T d hSourceI hSourceJ

example : trivialCofibrations (SequentialSpectrum V T) =
    (GenericSequentialLevel.originalGenerators T d.J).rlp.llp :=
  GenericSequentialLevel.original_trivialCofibrations_eq T d hSourceI hSourceJ

example (n : ℕ) : (SequentialSpectrum.freeAtEvaluationAdjunction T n).IsQuillenAdjunction :=
  GenericSequentialLevel.original_freeAtEvaluation_isQuillenAdjunction T d hSourceI hSourceJ n

example : FunctorialFactorizationData (cofibrations (SequentialSpectrum V T))
    (trivialFibrations (SequentialSpectrum V T)) :=
  GenericSequentialLevel.originalCofibrantFactorizationData T d hSourceI hSourceJ

example : FunctorialFactorizationData (trivialCofibrations (SequentialSpectrum V T))
    (fibrations (SequentialSpectrum V T)) :=
  GenericSequentialLevel.originalFibrantFactorizationData T d hSourceI hSourceJ

end GenericLevel

universe u v

private abbrev Sequential := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev family := PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

namespace NativeLevel

private def selectedModel : ModelCategory Sequential.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := Index.{u, v}) (B := B)

local instance : ModelCategory Sequential.{u, v} := selectedModel (B := B)

example : weakEquivalences Sequential.{u, v} =
    EvaluationTransfer.evaluationProperty
      (fun b : Index.{u, v} => EnrichedFunctorCat.evaluation b)
      (weakEquivalences PointedCGWH.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq (A := Index.{u, v}) (B := B)

example : fibrations Sequential.{u, v} =
    EvaluationTransfer.evaluationProperty
      (fun b : Index.{u, v} => EnrichedFunctorCat.evaluation b)
      (fibrations PointedCGWH.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.fibrations_eq (A := Index.{u, v}) (B := B)

example : cofibrations Sequential.{u, v} =
    (generators (A := Index.{u, v}) PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp :=
  HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq (A := Index.{u, v}) (B := B)

example : trivialCofibrations Sequential.{u, v} =
    (generators (A := Index.{u, v}) PointedCGWH.realizedHornInclusions.{u, v}).rlp.llp :=
  HomotopicalAlgebra.EnrichedProjective.Native.trivialCofibrations_eq (A := Index.{u, v}) (B := B)

example : trivialFibrations Sequential.{u, v} =
    EvaluationTransfer.evaluationProperty
      (fun b : Index.{u, v} => EnrichedFunctorCat.evaluation b)
      (trivialFibrations PointedCGWH.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.trivialFibrations_eq (A := Index.{u, v}) (B := B)

example : CofibrantGenerationData Sequential.{u, v} realizedGeneratorCardinal.{v} :=
  PointedCGWH.Spectra.CanonicalGeneration.sequential (B := B)

example : (PointedCGWH.Spectra.CanonicalGeneration.sequential (B := B)).I =
    adjointFamilyGenerators
      (fun n : ℕ => EnrichedFunctorCat.Free.functor
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n))
      PointedCGWH.realizedBoundaryInclusions.{u, v} :=
  PointedCGWH.Spectra.CanonicalGeneration.sequential_I (B := B)

example : (PointedCGWH.Spectra.CanonicalGeneration.sequential (B := B)).J =
    adjointFamilyGenerators
      (fun n : ℕ => EnrichedFunctorCat.Free.functor
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n))
      PointedCGWH.realizedHornInclusions.{u, v} :=
  PointedCGWH.Spectra.CanonicalGeneration.sequential_J (B := B)

example : LeftBousfieldLocalizationData
    PointedCGWH.Spectra.NativeStableModelConsumers.sequentialStabilizationArrows.{u, v} :=
  PointedCGWH.Spectra.NativeStableModelConsumers.sequentialLeftBousfieldLocalizationData (B := B)

end NativeLevel

namespace Stable

open PointedCGWH.Spectra.NativeStableModels

private def selectedModel : ModelCategory Sequential.{u, v} :=
  sequentialModelCategory (B := B)

local instance : ModelCategory Sequential.{u, v} := selectedModel (B := B)

example : weakEquivalences Sequential.{u, v} = NativeK.omegaTests family.{u, v} ∧
    cofibrations Sequential.{u, v} = (NativeK.levelI (I := Index.{u, v})).rlp.llp ∧
    fibrations Sequential.{u, v} = (NativeK.generators family.{u, v}).rlp ∧
    trivialCofibrations Sequential.{u, v} = (NativeK.generators family.{u, v}).rlp.llp ∧
    trivialFibrations Sequential.{u, v} = (NativeK.levelI (I := Index.{u, v})).rlp :=
  HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.sequential_five_classes (B := B)

example (X : Sequential.{u, v}) : IsFibrant X ↔ NativeK.IsOmega family.{u, v} X :=
  HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.sequential_isFibrant_iff_isOmega
    (B := B) X

example : CofibrantGenerationData Sequential.{u, v} realizedGeneratorCardinal.{v} :=
  sequentialGenerationData (B := B)

example : (sequentialGenerationData (B := B)).I = NativeK.levelI (I := Index.{u, v}) ∧
    (sequentialGenerationData (B := B)).J = NativeK.generators family.{u, v} :=
  ⟨rfl, rfl⟩

example : FunctorialFactorizationData (cofibrations Sequential.{u, v})
    (trivialFibrations Sequential.{u, v}) := sequentialIFactorizationData (B := B)

example : FunctorialFactorizationData (trivialCofibrations Sequential.{u, v})
    (fibrations Sequential.{u, v}) := sequentialKFactorizationData (B := B)

example : HasFunctorialFactorization (cofibrations Sequential.{u, v})
    (trivialFibrations Sequential.{u, v}) ∧
    HasFunctorialFactorization (trivialCofibrations Sequential.{u, v})
      (fibrations Sequential.{u, v}) :=
  sequential_functorialFactorizations (B := B)

example : (sequentialIFactorizationData (B := B)).Z =
    (OriginalFactorizationAssembly.originalI (A := Index.{u, v}) (B := B)).Z ∧
    (sequentialIFactorizationData (B := B)).i =
    (OriginalFactorizationAssembly.originalI (A := Index.{u, v}) (B := B)).i ∧
    (sequentialIFactorizationData (B := B)).p =
    (OriginalFactorizationAssembly.originalI (A := Index.{u, v}) (B := B)).p :=
  sequentialI_original_fields (B := B)

example : (sequentialKFactorizationData (B := B)).Z = (NativeK.factorizationData family.{u, v}).Z ∧
    (sequentialKFactorizationData (B := B)).i = (NativeK.factorizationData family.{u, v}).i ∧
    (sequentialKFactorizationData (B := B)).p = (NativeK.factorizationData family.{u, v}).p :=
  sequentialK_original_fields (B := B)

attribute [local instance] Native.generatorsI_isCardinalForSmallObjectArgument
  NativeK.generators_isCardinalForSmallObjectArgument

example (F : Arrow Sequential.{u, v}) :
    (sequentialIFactorizationData (B := B)).Z.obj F =
      SmallObject.obj (NativeK.levelI (I := Index.{u, v})) realizedGeneratorCardinal.{v} F.hom ∧
    (sequentialKFactorizationData (B := B)).Z.obj F =
      SmallObject.obj (NativeK.generators family.{u, v}) realizedGeneratorCardinal.{v} F.hom :=
  sequential_factorization_objects (B := B) F

example {F G : Arrow Sequential.{u, v}} (φ : F ⟶ G) :
    (sequentialIFactorizationData (B := B)).Z.map φ =
      SmallObject.objMap (NativeK.levelI (I := Index.{u, v})) realizedGeneratorCardinal.{v} φ ∧
    (sequentialKFactorizationData (B := B)).Z.map φ =
      SmallObject.objMap (NativeK.generators family.{u, v}) realizedGeneratorCardinal.{v} φ :=
  sequential_factorization_maps (B := B) φ

example (F : Arrow Sequential.{u, v}) :
    (sequentialIFactorizationData (B := B)).i.app F =
      SmallObject.ιObj (NativeK.levelI (I := Index.{u, v})) realizedGeneratorCardinal.{v} F.hom ∧
    (sequentialIFactorizationData (B := B)).p.app F =
      SmallObject.πObj (NativeK.levelI (I := Index.{u, v})) realizedGeneratorCardinal.{v} F.hom ∧
    (sequentialKFactorizationData (B := B)).i.app F =
      SmallObject.ιObj (NativeK.generators family.{u, v}) realizedGeneratorCardinal.{v} F.hom ∧
    (sequentialKFactorizationData (B := B)).p.app F =
      SmallObject.πObj (NativeK.generators family.{u, v}) realizedGeneratorCardinal.{v} F.hom :=
  sequential_factorization_legs (B := B) F

example (F : Arrow Sequential.{u, v}) :
    (sequentialIFactorizationData (B := B)).i.app F ≫
      (sequentialIFactorizationData (B := B)).p.app F = F.hom ∧
    (sequentialKFactorizationData (B := B)).i.app F ≫
      (sequentialKFactorizationData (B := B)).p.app F = F.hom :=
  sequential_factorization_fac (B := B) F

example {F G : Arrow Sequential.{u, v}} (φ : F ⟶ G) :
    (sequentialIFactorizationData (B := B)).i.app F ≫
      (sequentialIFactorizationData (B := B)).Z.map φ =
      φ.left ≫ (sequentialIFactorizationData (B := B)).i.app G ∧
    (sequentialIFactorizationData (B := B)).Z.map φ ≫
      (sequentialIFactorizationData (B := B)).p.app G =
      (sequentialIFactorizationData (B := B)).p.app F ≫ φ.right ∧
    (sequentialKFactorizationData (B := B)).i.app F ≫
      (sequentialKFactorizationData (B := B)).Z.map φ =
      φ.left ≫ (sequentialKFactorizationData (B := B)).i.app G ∧
    (sequentialKFactorizationData (B := B)).Z.map φ ≫
      (sequentialKFactorizationData (B := B)).p.app G =
      (sequentialKFactorizationData (B := B)).p.app F ≫ φ.right :=
  sequential_factorization_naturality (B := B) φ

example : (selectedModel (B := B)).categoryWithCofibrations.cofibrations =
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
      (A := Index.{u, v}) (B := B)).categoryWithCofibrations.cofibrations :=
  sequential_cofibrations_eq_level (B := B)

example : (sequentialLevelToStableAdjunction (B := B)).IsQuillenAdjunction :=
  sequentialLevelToStable_isQuillen (B := B)

example : sequentialCofibrantReplacement.{u, v} = Replacement.cofibrantReplacement (A := Index.{u, v}) ∧
    sequentialInitialToQ.{u, v} = Replacement.initialToCofibrantReplacement (A := Index.{u, v}) ∧
    sequentialQCounit.{u, v} = Replacement.cofibrantReplacementCounit (A := Index.{u, v}) ∧
    sequentialFibrantReplacement.{u, v} = NativeK.omegaReplacement family.{u, v} ∧
    sequentialRUnit.{u, v} = NativeK.omegaReplacementUnit family.{u, v} ∧
    sequentialRToZero.{u, v} = Functor.whiskerLeft Diagrams.toZeroArrow
      (NativeK.factorizationData family.{u, v}).p :=
  sequential_replacement_original_fields (B := B)

example (X : Sequential.{u, v}) : IsCofibrant (sequentialCofibrantReplacement.obj X) :=
  sequentialQ_isCofibrant (B := B) X

example (X : Sequential.{u, v}) :
    trivialFibrations Sequential.{u, v} (sequentialQCounit.app X) :=
  sequentialQCounit_trivialFibration (B := B) X

example (X : Sequential.{u, v}) : IsFibrant (sequentialFibrantReplacement.obj X) :=
  sequentialR_isFibrant (B := B) X

example (X : Sequential.{u, v}) :
    trivialCofibrations Sequential.{u, v} (sequentialRUnit.app X) :=
  sequentialRUnit_trivialCofibration (B := B) X

example (X : Sequential.{u, v}) :
    sequentialInitialToQ.app X ≫ sequentialQCounit.app X = Diagrams.zeroTo X ∧
    sequentialRUnit.app X ≫ sequentialRToZero.app X = Diagrams.toZero X :=
  sequential_replacement_fac (B := B) X

example {X Y : Sequential.{u, v}} (f : X ⟶ Y) :
    sequentialCofibrantReplacement.map f ≫ sequentialQCounit.app Y = sequentialQCounit.app X ≫ f ∧
    f ≫ sequentialRUnit.app Y = sequentialRUnit.app X ≫ sequentialFibrantReplacement.map f :=
  sequential_replacement_naturality (B := B) f

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableLocalizationGeometry
open PointedCGWH.Spectra.NativeStableModels.SequentialStableModelProperties

example {X Y : Sequential.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Sequential.{u, v} f ↔ ∀ q : ℤ, IsIso ((integerStablePiFunctor q).map f) :=
  weakEquivalences_iff_integerPi (B := B) f

example : IsLeftProper Sequential.{u, v} ∧ IsRightProper Sequential.{u, v} :=
  sequentialModel_isProper (B := B)

example : stableProjection.{u, v} ⋙ integerHoEquivalence.functor ≅ integerStableProjection :=
  integerHoProjectionIso (B := B)

example (q : ℤ) : stableProjection.{u, v} ⋙ integerPiHoFunctor q ≅ integerStablePiFunctor q :=
  integerPiHoSourceIso (B := B) q

example {X Y : StableHomotopyCategory.{u, v}} (f : X ⟶ Y) :
    (∀ q : ℤ, IsIso ((integerPiHoFunctor q).map f)) ↔ IsIso f :=
  integerPiHoFunctor_jointly_reflects_isomorphisms (B := B) f

end Stable

namespace IndexComparisons

open PointedCGWH.Spectra.NativeIndexKanComposition
open PointedCGWH.Spectra.NativeStableIndexAdjunctions
open PointedCGWH.Spectra.Orthogonal.IndexKan.NativeStableIndexComparisons

attribute [local instance]
  HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.sequentialModelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetricModelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.orthogonalModelCategory

example : sequentialSymmetricAdjunction.{u, v}.IsQuillenAdjunction :=
  sequentialSymmetric_stable_isQuillen (B := B)

example : sequentialOrthogonalAdjunction.{u, v}.IsQuillenAdjunction :=
  sequentialOrthogonal_stable_isQuillen (B := B)

example : symmetricOrthogonalAdjunction.{u, v}.IsQuillenAdjunction :=
  symmetricOrthogonal_stable_isQuillen (B := B)

example {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Actual.OrthogonalCarrier.{u, v} f ↔
      weakEquivalences Sequential.{u, v} (sequentialRightDerivedRestriction.map f) :=
  sequentialRightDerivedRestriction_stableWeak_iff (B := B) f

example {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Actual.OrthogonalCarrier.{u, v} f ↔
      weakEquivalences Actual.SymmetricCarrier.{u, v} (symmetricRightDerivedRestriction.map f) :=
  symmetricRightDerivedRestriction_stableWeak_iff (B := B) f

example (X : Actual.OrthogonalCarrier.{u, v}) :
    IsFibrant (sequentialOrthogonalRestriction.obj X) ↔ IsFibrant X :=
  sequentialRestriction_isFibrant_iff (B := B) X

example (X : Actual.OrthogonalCarrier.{u, v}) :
    IsFibrant (symmetricOrthogonalRestriction.obj X) ↔ IsFibrant X :=
  symmetricRestriction_isFibrant_iff (B := B) X

example {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) [IsFibrant X] [IsFibrant Y] :
    weakEquivalences Sequential.{u, v} (sequentialOrthogonalRestriction.map f) ↔
      weakEquivalences Actual.OrthogonalCarrier.{u, v} f :=
  sequentialRestriction_stableWeak_iff_of_isFibrant (B := B) f

example {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) [IsFibrant X] [IsFibrant Y] :
    weakEquivalences Actual.SymmetricCarrier.{u, v} (symmetricOrthogonalRestriction.map f) ↔
      weakEquivalences Actual.OrthogonalCarrier.{u, v} f :=
  symmetricRestriction_stableWeak_iff_of_isFibrant (B := B) f

end IndexComparisons

end MathlibExtTest.AlgebraicTopology.Spectra.SequentialModelAPI

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableModelConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableModelConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.PositiveStabilizationK
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeSymmetricStableMonoidalModel
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeOrthogonalStableMonoidalModel
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeAllObjectSpectrumMonoidAxiom

/-!
# Symmetric and orthogonal spectrum model APIs

The native stable models determine the five model classes, cofibrant generation,
functorial factorizations and replacements. Their stable smash products satisfy
the pushout-product and unit axioms, and their all-object monoid axioms retain
the cellular universe condition. Positive indexing gives the symmetric positive
level model.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace MathlibExtTest.AlgebraicTopology.Spectra.SymmetricOrthogonalModelAPI

private abbrev Symmetric := Actual.SymmetricCarrier.{u, v}
private abbrev Orthogonal := Actual.OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

namespace Symmetric

open HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

attribute [local instance]
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

/-- The native symmetric stable model. -/
private def selectedModel : ModelCategory Symmetric.{u, v} :=
  symmetricModelCategory (B := B)

local instance : ModelCategory Symmetric.{u, v} := selectedModel (B := B)

example : weakEquivalences Symmetric.{u, v} = NativeK.omegaTests Actual.symmetricFamily.{u, v} ∧
    cofibrations Symmetric.{u, v} = (NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})).rlp.llp ∧
    fibrations Symmetric.{u, v} = (NativeK.generators Actual.symmetricFamily.{u, v}).rlp ∧
    trivialCofibrations Symmetric.{u, v} = (NativeK.generators Actual.symmetricFamily.{u, v}).rlp.llp ∧
    trivialFibrations Symmetric.{u, v} = (NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})).rlp :=
  symmetric_five_classes (B := B)

example : CofibrantGenerationData Symmetric.{u, v} realizedGeneratorCardinal.{v} :=
  symmetricGenerationData (B := B)

example : (symmetricGenerationData (B := B)).I =
    NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v}) ∧
    (symmetricGenerationData (B := B)).J = NativeK.generators Actual.symmetricFamily.{u, v} :=
  ⟨rfl, rfl⟩

example : FunctorialFactorizationData (cofibrations Symmetric.{u, v})
    (trivialFibrations Symmetric.{u, v}) := symmetricCofibrantFactorizationData (B := B)

example : FunctorialFactorizationData (trivialCofibrations Symmetric.{u, v})
    (fibrations Symmetric.{u, v}) := symmetricFibrantFactorizationData (B := B)

example : (symmetricCofibrantFactorizationData (B := B)).Z =
    (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) (B := B)).Z ∧
    (symmetricCofibrantFactorizationData (B := B)).i =
    (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) (B := B)).i ∧
    (symmetricCofibrantFactorizationData (B := B)).p =
    (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) (B := B)).p ∧
    (symmetricFibrantFactorizationData (B := B)).Z = (NativeK.factorizationData Actual.symmetricFamily.{u, v}).Z ∧
    (symmetricFibrantFactorizationData (B := B)).i = (NativeK.factorizationData Actual.symmetricFamily.{u, v}).i ∧
    (symmetricFibrantFactorizationData (B := B)).p = (NativeK.factorizationData Actual.symmetricFamily.{u, v}).p :=
  symmetricFactorizationData_original (B := B)

example : (symmetricLevelToStableAdjunction (B := B)).IsQuillenAdjunction :=
  symmetricLevelToStableAdjunction_isQuillen (B := B)

example : (selectedModel (B := B)).categoryWithCofibrations.cofibrations =
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) (B := B)).categoryWithCofibrations.cofibrations :=
  symmetric_cofibrations_eq_level (B := B)

example (X : Symmetric.{u, v}) :
    IsCofibrant ((symmetricCofibrantReplacement (B := B)).obj X) :=
  symmetricQ_isCofibrant (B := B) X

example (X : Symmetric.{u, v}) : trivialFibrations Symmetric.{u, v}
    ((symmetricCofibrantReplacementCounit (B := B)).app X) :=
  symmetricQCounit_trivialFibration (B := B) X

example (X : Symmetric.{u, v}) :
    IsFibrant ((symmetricFibrantReplacement (B := B)).obj X) :=
  symmetricR_isFibrant (B := B) X

example (X : Symmetric.{u, v}) : trivialCofibrations Symmetric.{u, v}
    ((symmetricFibrantReplacementUnit (B := B)).app X) :=
  symmetricRUnit_trivialCofibration (B := B) X

example (X : Symmetric.{u, v}) :
    (symmetricInitialToQ (B := B)).app X ≫ (symmetricCofibrantReplacementCounit (B := B)).app X =
      Diagrams.zeroTo X ∧
    (symmetricFibrantReplacementUnit (B := B)).app X ≫ (symmetricRToZero (B := B)).app X =
      Diagrams.toZero X := symmetric_replacement_fac (B := B) X

example {X Y : Symmetric.{u, v}} (f : X ⟶ Y) :
    (symmetricCofibrantReplacement (B := B)).map f ≫ (symmetricCofibrantReplacementCounit (B := B)).app Y =
      (symmetricCofibrantReplacementCounit (B := B)).app X ≫ f ∧
    f ≫ (symmetricFibrantReplacementUnit (B := B)).app Y =
      (symmetricFibrantReplacementUnit (B := B)).app X ≫ (symmetricFibrantReplacement (B := B)).map f :=
  symmetric_replacement_naturality (B := B) f

example : MonoidalPushoutProductAxiom Symmetric.{u, v} :=
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stablePushoutProductAxiom (B := B)

example : IsClosedSymmetricMonoidalModelCategory Symmetric.{u, v} :=
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stableSmashMonoidalModel (B := B)

example : MonoidalUnitAxiomWitness Symmetric.{u, v} :=
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stableUnitAxiomWitness (B := B)

example (X : Symmetric.{u, v}) (hX : IsCofibrant X) : weakEquivalences Symmetric.{u, v}
    ((leftUnitReplacementMap
      (PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stableUnitAxiomWitness (B := B)).q).app X) :=
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stableUnitReplacement_left (B := B) X hX

example (X : Symmetric.{u, v}) (hX : IsCofibrant X) : weakEquivalences Symmetric.{u, v}
    ((rightUnitReplacementMap
      (PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stableUnitAxiomWitness (B := B)).q).app X) :=
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.stableUnitReplacement_right (B := B) X hX

variable [UnivLE.{w, v}]

example : MonoidAxiom.{w} Symmetric.{u, v} :=
  PointedCGWH.Spectra.Symmetric.OriginalMonoidAxiom.originalStableMonoidAxiom (B := B)

end Symmetric

namespace Orthogonal

open HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

attribute [local instance]
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash.monoidalCategory
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash.symmetricCategory
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed.monoidalClosed

/-- The native orthogonal stable model. -/
private def selectedModel : ModelCategory Orthogonal.{u, v} :=
  orthogonalModelCategory (B := B)

local instance : ModelCategory Orthogonal.{u, v} := selectedModel (B := B)

example : weakEquivalences Orthogonal.{u, v} = NativeK.omegaTests Actual.orthogonalFamily.{u, v} ∧
    cofibrations Orthogonal.{u, v} =
      (NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})).rlp.llp ∧
    fibrations Orthogonal.{u, v} = (NativeK.generators Actual.orthogonalFamily.{u, v}).rlp ∧
    trivialCofibrations Orthogonal.{u, v} = (NativeK.generators Actual.orthogonalFamily.{u, v}).rlp.llp ∧
    trivialFibrations Orthogonal.{u, v} =
      (NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})).rlp :=
  orthogonal_five_classes (B := B)

example : CofibrantGenerationData Orthogonal.{u, v} realizedGeneratorCardinal.{v} :=
  orthogonalGenerationData (B := B)

example : (orthogonalGenerationData (B := B)).I =
    NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) ∧
    (orthogonalGenerationData (B := B)).J = NativeK.generators Actual.orthogonalFamily.{u, v} :=
  ⟨rfl, rfl⟩

example : FunctorialFactorizationData (cofibrations Orthogonal.{u, v})
    (trivialFibrations Orthogonal.{u, v}) := orthogonalCofibrantFactorizationData (B := B)

example : FunctorialFactorizationData (trivialCofibrations Orthogonal.{u, v})
    (fibrations Orthogonal.{u, v}) := orthogonalFibrantFactorizationData (B := B)

example : (orthogonalCofibrantFactorizationData (B := B)).Z =
    (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
      (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) (B := B)).Z ∧
    (orthogonalCofibrantFactorizationData (B := B)).i =
    (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
      (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) (B := B)).i ∧
    (orthogonalCofibrantFactorizationData (B := B)).p =
    (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
      (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) (B := B)).p ∧
    (orthogonalFibrantFactorizationData (B := B)).Z = (NativeK.factorizationData Actual.orthogonalFamily.{u, v}).Z ∧
    (orthogonalFibrantFactorizationData (B := B)).i = (NativeK.factorizationData Actual.orthogonalFamily.{u, v}).i ∧
    (orthogonalFibrantFactorizationData (B := B)).p = (NativeK.factorizationData Actual.orthogonalFamily.{u, v}).p :=
  orthogonalFactorizationData_original (B := B)

example : (orthogonalLevelToStableAdjunction (B := B)).IsQuillenAdjunction :=
  orthogonalLevelToStableAdjunction_isQuillen (B := B)

example : (selectedModel (B := B)).categoryWithCofibrations.cofibrations =
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
      (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) (B := B)).categoryWithCofibrations.cofibrations :=
  orthogonal_cofibrations_eq_level (B := B)

example (X : Orthogonal.{u, v}) :
    IsCofibrant ((orthogonalCofibrantReplacement (B := B)).obj X) :=
  orthogonalQ_isCofibrant (B := B) X

example (X : Orthogonal.{u, v}) : trivialFibrations Orthogonal.{u, v}
    ((orthogonalCofibrantReplacementCounit (B := B)).app X) :=
  orthogonalQCounit_trivialFibration (B := B) X

example (X : Orthogonal.{u, v}) :
    IsFibrant ((orthogonalFibrantReplacement (B := B)).obj X) :=
  orthogonalR_isFibrant (B := B) X

example (X : Orthogonal.{u, v}) : trivialCofibrations Orthogonal.{u, v}
    ((orthogonalFibrantReplacementUnit (B := B)).app X) :=
  orthogonalRUnit_trivialCofibration (B := B) X

example (X : Orthogonal.{u, v}) :
    (orthogonalInitialToQ (B := B)).app X ≫ (orthogonalCofibrantReplacementCounit (B := B)).app X =
      Diagrams.zeroTo X ∧
    (orthogonalFibrantReplacementUnit (B := B)).app X ≫ (orthogonalRToZero (B := B)).app X =
      Diagrams.toZero X := orthogonal_replacement_fac (B := B) X

example {X Y : Orthogonal.{u, v}} (f : X ⟶ Y) :
    (orthogonalCofibrantReplacement (B := B)).map f ≫ (orthogonalCofibrantReplacementCounit (B := B)).app Y =
      (orthogonalCofibrantReplacementCounit (B := B)).app X ≫ f ∧
    f ≫ (orthogonalFibrantReplacementUnit (B := B)).app Y =
      (orthogonalFibrantReplacementUnit (B := B)).app X ≫ (orthogonalFibrantReplacement (B := B)).map f :=
  orthogonal_replacement_naturality (B := B) f

example : MonoidalPushoutProductAxiom Orthogonal.{u, v} :=
  PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash.stablePushoutProductAxiom (B := B)

example : IsClosedSymmetricMonoidalModelCategory Orthogonal.{u, v} :=
  PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash.stableSmashMonoidalModel (B := B)

example : MonoidalUnitAxiomWitness Orthogonal.{u, v} :=
  PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash.stableUnitAxiomWitness (B := B)

example (X : Orthogonal.{u, v}) (hX : IsCofibrant X) : weakEquivalences Orthogonal.{u, v}
    ((leftUnitReplacementMap
      (PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash.stableUnitAxiomWitness (B := B)).q).app X) :=
  PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash.stableUnitReplacement_left (B := B) X hX

example (X : Orthogonal.{u, v}) (hX : IsCofibrant X) : weakEquivalences Orthogonal.{u, v}
    ((rightUnitReplacementMap
      (PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash.stableUnitAxiomWitness (B := B)).q).app X) :=
  PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash.stableUnitReplacement_right (B := B) X hX

variable [UnivLE.{w, v}]

example : MonoidAxiom.{w} Orthogonal.{u, v} :=
  PointedCGWH.Spectra.Orthogonal.OriginalMonoidAxiomComplete.originalStableMonoidAxiom (B := B)

end Orthogonal

namespace SymmetricPositiveLevel

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.ActualPositive

local instance : ModelCategory Symmetric.{u, v} := levelModel (B := B)

example : CofibrantGenerationData Symmetric.{u, v} realizedGeneratorCardinal.{v} :=
  generationData (B := B)

example (n : ℕ+) : index.{u, v} n =
    PointedCGWH.symmetricOperatorObj (CategoryTheory.Operad.SmallFinBijGroupoid.card n) := rfl

example (n : ℕ+) : oneStepFamily.{u, v}.source n =
    PointedCGWH.symmetricOperatorObj (CategoryTheory.Operad.SmallFinBijGroupoid.card n) ∧
    oneStepFamily.{u, v}.target n = PointedCGWH.symmetricOperatorObj
      (CategoryTheory.Operad.SmallFinBijGroupoid.card n ⊗ CategoryTheory.Operad.SmallFinBijGroupoid.card 1) :=
  oneStepFamily_objects n

end SymmetricPositiveLevel

end MathlibExtTest.AlgebraicTopology.Spectra.SymmetricOrthogonalModelAPI

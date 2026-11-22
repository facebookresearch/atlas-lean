/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalFactorizations
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.ConditionalQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableFiberHomNullity
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses

/-!
# Native orthogonal stable model from the original I and K records

The actual all-arrow I-right class is recognized by the original caller
fiber and every Omega Hom test. The original K-left acyclicity and the
same original functorial factor records then construct this stable model
on the full native enriched orthogonal spectrum carrier.

The original cardinal, bottom, all five map classes, full generator
families, complete factor functors and natural maps are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory ZeroObject

namespace HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.OriginalFiberNullity

open OperatorStabilizationK
open PointedCGWH.Spectra.Orthogonal.NativeStableModels
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev orthogonalIndex := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev orthogonalFamily := Actual.orthogonalFamily.{u, v}
private instance orthogonalFiniteLimits : HasFiniteLimits Actual.OrthogonalCarrier.{u, v} :=
  (Native.modelCategory (B := B) (A := orthogonalIndex)).cm1a
private instance orthogonalFiniteColimits : HasFiniteColimits Actual.OrthogonalCarrier.{u, v} :=
  (Native.modelCategory (B := B) (A := orthogonalIndex)).cm1b

theorem orthogonal_right_class_eq :
    (NativeK.levelI (I := orthogonalIndex)).rlp =
      (NativeK.generators orthogonalFamily).rlp ⊓ NativeK.omegaTests orthogonalFamily :=
  ConditionalRecognition.right_class_eq
    (orthogonalComparisonHomBijections (B := B))

theorem orthogonal_left_class_eq :
    (NativeK.generators orthogonalFamily).rlp.llp =
      (NativeK.levelI (I := orthogonalIndex)).rlp.llp ⊓ NativeK.omegaTests orthogonalFamily :=
  ConditionalRecognition.left_class_eq
    (orthogonalComparisonHomBijections (B := B))

/-- The stable model on the native orthogonal carrier from the original I and K records. -/
@[instance_reducible]
def orthogonalModelCategory : ModelCategory Actual.OrthogonalCarrier.{u, v} :=
  ConditionalModel.modelCategory
    (orthogonalComparisonHomBijections (B := B))

theorem orthogonal_five_classes :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    weakEquivalences Actual.OrthogonalCarrier.{u, v} = NativeK.omegaTests orthogonalFamily ∧
      cofibrations Actual.OrthogonalCarrier.{u, v} =
        (NativeK.levelI (I := orthogonalIndex)).rlp.llp ∧
      fibrations Actual.OrthogonalCarrier.{u, v} = (NativeK.generators orthogonalFamily).rlp ∧
      trivialCofibrations Actual.OrthogonalCarrier.{u, v} =
        (NativeK.generators orthogonalFamily).rlp.llp ∧
      trivialFibrations Actual.OrthogonalCarrier.{u, v} =
        (NativeK.levelI (I := orthogonalIndex)).rlp :=
  ConditionalModel.five_classes (orthogonalComparisonHomBijections (B := B))

theorem orthogonal_isFibrant_iff_isOmega (X : Actual.OrthogonalCarrier.{u, v}) :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    IsFibrant X ↔ NativeK.IsOmega orthogonalFamily X :=
  ConditionalModel.isFibrant_iff_isOmega (orthogonalComparisonHomBijections (B := B)) X

/-- Cofibrant generation at the original cardinal for the native orthogonal stable model. -/
def orthogonalGenerationData :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    CofibrantGenerationData Actual.OrthogonalCarrier.{u, v} realizedGeneratorCardinal.{v} :=
  ConditionalModel.generationData
    (orthogonalComparisonHomBijections (B := B))
/-- Both actual stable factor records retain the original native construction. -/
def orthogonalCofibrantFactorizationData :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    FunctorialFactorizationData (cofibrations Actual.OrthogonalCarrier.{u, v})
      (trivialFibrations Actual.OrthogonalCarrier.{u, v}) := by
  let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
  exact ConditionalFactorizations.IFactorizationData
    (orthogonalComparisonHomBijections (B := B))

/-- The stable fibration factor retains the entire original paired K factor. -/
def orthogonalFibrantFactorizationData :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    FunctorialFactorizationData (trivialCofibrations Actual.OrthogonalCarrier.{u, v})
      (fibrations Actual.OrthogonalCarrier.{u, v}) := by
  let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
  exact ConditionalFactorizations.KFactorizationData
    (orthogonalComparisonHomBijections (B := B))

/-- Both full original middle functors and all four natural factor arrows are unchanged. -/
theorem orthogonalFactorizationData_original :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    orthogonalCofibrantFactorizationData.Z =
        (Native.cofibrantFactorizationData (B := B) (A := orthogonalIndex)).Z ∧
      orthogonalCofibrantFactorizationData.i =
        (Native.cofibrantFactorizationData (B := B) (A := orthogonalIndex)).i ∧
      orthogonalCofibrantFactorizationData.p =
        (Native.cofibrantFactorizationData (B := B) (A := orthogonalIndex)).p ∧
      orthogonalFibrantFactorizationData.Z = (NativeK.factorizationData orthogonalFamily).Z ∧
      orthogonalFibrantFactorizationData.i = (NativeK.factorizationData orthogonalFamily).i ∧
      orthogonalFibrantFactorizationData.p = (NativeK.factorizationData orthogonalFamily).p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The original zero-arrow families and retained factors construct both stable replacements. -/
def orthogonalCofibrantReplacement :
    Actual.OrthogonalCarrier.{u, v} ⥤ Actual.OrthogonalCarrier.{u, v} :=
  PointedCGWH.Spectra.Orthogonal.NativeStableModels.cofibrantReplacement (B := B)

/-- The fibrant replacement functor given by the original paired K factorization. -/
def orthogonalFibrantReplacement :
    Actual.OrthogonalCarrier.{u, v} ⥤ Actual.OrthogonalCarrier.{u, v} :=
  PointedCGWH.Spectra.Orthogonal.NativeStableModels.fibrantReplacement (B := B)

/-- The full replacement projection is the original I right-factor transformation. -/
def orthogonalCofibrantReplacementCounit :
    orthogonalCofibrantReplacement ⟶ 𝟭 Actual.OrthogonalCarrier.{u, v} :=
  PointedCGWH.Spectra.Orthogonal.NativeStableModels.qCounit (B := B)

/-- The full replacement unit is the original paired K left-factor transformation. -/
def orthogonalFibrantReplacementUnit :
    𝟭 Actual.OrthogonalCarrier.{u, v} ⟶ orthogonalFibrantReplacement :=
  PointedCGWH.Spectra.Orthogonal.NativeStableModels.rUnit (B := B)

/-- Both complete replacement functors are the original native Q and paired Omega replacement. -/
theorem orthogonalReplacement_original :
    orthogonalCofibrantReplacement =
        Replacement.cofibrantReplacement (B := B) (A := orthogonalIndex) ∧
      orthogonalFibrantReplacement = NativeK.omegaReplacement orthogonalFamily ∧
      orthogonalCofibrantReplacementCounit =
        Replacement.cofibrantReplacementCounit (B := B) (A := orthogonalIndex) ∧
      orthogonalFibrantReplacementUnit = NativeK.omegaReplacementUnit orthogonalFamily :=
  ⟨rfl, rfl, rfl, rfl⟩
/-- The identity compares the original level and this actual stable value. -/
def orthogonalLevelToStableAdjunction :
    ExplicitModelIdentity.comparison
        (Native.modelCategory (B := B) (A := orthogonalIndex)) orthogonalModelCategory ⊣
      ExplicitModelIdentity.comparison orthogonalModelCategory
        (Native.modelCategory (B := B) (A := orthogonalIndex)) :=
  ConditionalQuillen.adjunction
    (orthogonalComparisonHomBijections (B := B))

/-- Actual cofibration equality and native level weakness give the identity Quillen pair. -/
theorem orthogonalLevelToStableAdjunction_isQuillen :
    orthogonalLevelToStableAdjunction.IsQuillenAdjunction :=
  ConditionalQuillen.isQuillen
    (orthogonalComparisonHomBijections (B := B))

/-- The two stable weak factorization systems use those exact original factor records. -/
theorem orthogonal_functorialFactorizations :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    HasFunctorialFactorization (cofibrations Actual.OrthogonalCarrier.{u, v})
        (trivialFibrations Actual.OrthogonalCarrier.{u, v}) ∧
      HasFunctorialFactorization (trivialCofibrations Actual.OrthogonalCarrier.{u, v})
        (fibrations Actual.OrthogonalCarrier.{u, v}) :=
  ConditionalFactorizations.functorialFactorizations
    (orthogonalComparisonHomBijections (B := B))

/-- All actual stable cofibrations are the unchanged native projective cofibrations. -/
theorem orthogonal_cofibrations_eq_level :
    orthogonalModelCategory.{u, v}.categoryWithCofibrations.cofibrations =
      (Native.modelCategory (B := B) (A := orthogonalIndex)).categoryWithCofibrations.cofibrations :=
  ConditionalModel.cofibrations_eq_level
    (orthogonalComparisonHomBijections (B := B))

/-- The complete original I left leg keeps the same native zero source. -/
def orthogonalInitialToQ :
    (Functor.const Actual.OrthogonalCarrier.{u, v}).obj Diagrams.zeroDiagram ⟶
      orthogonalCofibrantReplacement :=
  PointedCGWH.Spectra.Orthogonal.NativeStableModels.initialToQ (B := B)

/-- The complete original K right leg keeps the same native zero target. -/
def orthogonalRToZero : orthogonalFibrantReplacement ⟶
    (Functor.const Actual.OrthogonalCarrier.{u, v}).obj Diagrams.zeroDiagram :=
  PointedCGWH.Spectra.Orthogonal.NativeStableModels.rToZero (B := B)

/-- Both remaining entire replacement arrows retain the actual native I and K values. -/
theorem orthogonalReplacement_zero_legs :
    orthogonalInitialToQ = Replacement.initialToCofibrantReplacement
        (B := B) (A := orthogonalIndex) ∧
      orthogonalRToZero = Functor.whiskerLeft Diagrams.toZeroArrow
        (NativeK.factorizationData orthogonalFamily).p := ⟨rfl, rfl⟩

/-- The actual original I output is cofibrant in this same stable model. -/
theorem orthogonalQ_isCofibrant (X : Actual.OrthogonalCarrier.{u, v}) :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    IsCofibrant (orthogonalCofibrantReplacement.obj X) := by
  let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
  change IsCofibrant (orthogonalCofibrantReplacement.obj X)
  rw [isCofibrant_iff_of_isInitial (orthogonalInitialToQ.app X) Diagrams.zeroDiagramIsInitial]
  exact (cofibration_iff (orthogonalInitialToQ.app X)).mpr
    (orthogonalCofibrantFactorizationData.hi (Diagrams.fromZeroArrow.obj X))

/-- The actual original I counit is a stable trivial fibration at every input. -/
theorem orthogonalQCounit_trivialFibration (X : Actual.OrthogonalCarrier.{u, v}) :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    trivialFibrations Actual.OrthogonalCarrier.{u, v}
      (orthogonalCofibrantReplacementCounit.app X) :=
  orthogonalCofibrantFactorizationData.hp (Diagrams.fromZeroArrow.obj X)

/-- The original full-family K output is fibrant in this exact stable model. -/
theorem orthogonalR_isFibrant (X : Actual.OrthogonalCarrier.{u, v}) :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    IsFibrant (orthogonalFibrantReplacement.obj X) := by
  let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
  change IsFibrant (orthogonalFibrantReplacement.obj X)
  exact (orthogonal_isFibrant_iff_isOmega _).mpr
    (NativeK.omegaReplacement_isOmega orthogonalFamily X)

/-- The actual original K unit is a stable trivial cofibration at every input. -/
theorem orthogonalRUnit_trivialCofibration (X : Actual.OrthogonalCarrier.{u, v}) :
    let : ModelCategory Actual.OrthogonalCarrier.{u, v} := orthogonalModelCategory
    trivialCofibrations Actual.OrthogonalCarrier.{u, v}
      (orthogonalFibrantReplacementUnit.app X) :=
  orthogonalFibrantFactorizationData.hi (Diagrams.toZeroArrow.obj X)

/-- Both actual replacement factors give the original zero-arrow equations. -/
theorem orthogonal_replacement_fac (X : Actual.OrthogonalCarrier.{u, v}) :
    orthogonalInitialToQ.app X ≫ orthogonalCofibrantReplacementCounit.app X = Diagrams.zeroTo X ∧
      orthogonalFibrantReplacementUnit.app X ≫ orthogonalRToZero.app X = Diagrams.toZero X :=
  ⟨orthogonalCofibrantFactorizationData.fac_app, orthogonalFibrantFactorizationData.fac_app⟩

/-- Both original full replacement functors retain every original input-arrow square. -/
theorem orthogonal_replacement_naturality {X Y : Actual.OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    orthogonalCofibrantReplacement.map f ≫ orthogonalCofibrantReplacementCounit.app Y =
        orthogonalCofibrantReplacementCounit.app X ≫ f ∧
      f ≫ orthogonalFibrantReplacementUnit.app Y =
        orthogonalFibrantReplacementUnit.app X ≫ orthogonalFibrantReplacement.map f :=
  ⟨orthogonalCofibrantReplacementCounit.naturality f, orthogonalFibrantReplacementUnit.naturality f⟩

end HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

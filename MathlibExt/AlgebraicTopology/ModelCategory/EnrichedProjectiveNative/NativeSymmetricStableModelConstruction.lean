/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableRightClass
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses

/-!
# The original native symmetric stable model and localization recognition

The imported original caller-fiber/nullity provider supplies the complete
I/K class identities through the genuine closed forward integer detector.

The original I/K right and left classes, complete same-cardinal factor records,
and all-source acyclicity then construct the native stable model. Its five
classes, original factor functors and maps, replacements, and identity Quillen
pair use the unchanged actual symmetric carrier and caller bottom.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory ZeroObject

namespace HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

open OperatorStabilizationK
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev symmetricIndex := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev symmetricFamily := Actual.symmetricFamily.{u, v}
private instance symmetricFiniteLimits : HasFiniteLimits Actual.SymmetricCarrier.{u, v} :=
  (Native.modelCategory (B := B) (A := symmetricIndex)).cm1a
private instance symmetricFiniteColimits : HasFiniteColimits Actual.SymmetricCarrier.{u, v} :=
  (Native.modelCategory (B := B) (A := symmetricIndex)).cm1b

/-- The complete original I/K factor records and genuine class recognition construct the native stable model. -/
@[instance_reducible]
def symmetricModelCategory : ModelCategory Actual.SymmetricCarrier.{u, v} :=
  OriginalGeneratedModel.modelCategory
    (NativeK.levelI (I := symmetricIndex)) (NativeK.generators symmetricFamily)
    (NativeK.omegaTests symmetricFamily) inferInstance symmetric_right_class_eq
    PointedCGWH.Spectra.NativeStable.symmetricKLeft_le_omegaTests
    (OriginalFactorizationAssembly.originalI (B := B) (A := symmetricIndex))
    (NativeK.factorizationData symmetricFamily)

theorem symmetric_five_classes :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    weakEquivalences Actual.SymmetricCarrier.{u, v} = NativeK.omegaTests symmetricFamily ∧
      cofibrations Actual.SymmetricCarrier.{u, v} = (NativeK.levelI (I := symmetricIndex)).rlp.llp ∧
      fibrations Actual.SymmetricCarrier.{u, v} = (NativeK.generators symmetricFamily).rlp ∧
      trivialCofibrations Actual.SymmetricCarrier.{u, v} = (NativeK.generators symmetricFamily).rlp.llp ∧
      trivialFibrations Actual.SymmetricCarrier.{u, v} = (NativeK.levelI (I := symmetricIndex)).rlp :=
  OriginalGeneratedModel.five_classes
    (NativeK.levelI (I := symmetricIndex)) (NativeK.generators symmetricFamily)
    (NativeK.omegaTests symmetricFamily) inferInstance symmetric_right_class_eq
    PointedCGWH.Spectra.NativeStable.symmetricKLeft_le_omegaTests
    (OriginalFactorizationAssembly.originalI (B := B) (A := symmetricIndex))
    (NativeK.factorizationData symmetricFamily)

theorem symmetric_isFibrant_iff_isOmega (X : Actual.SymmetricCarrier.{u, v}) :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    IsFibrant X ↔ NativeK.IsOmega symmetricFamily X := by
  let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
  change IsFibrant X ↔ NativeK.IsOmega symmetricFamily X
  rw [isFibrant_iff_of_isTerminal (Diagrams.toZero X) Diagrams.zeroDiagramIsTerminal]
  rw [fibration_iff, symmetric_five_classes.2.2.1]
  exact NativeK.lifting_toZero_iff_isOmega symmetricFamily X

/-- The original full I and paired K generators use the same realized cardinal and arbitrary caller bottom. -/
def symmetricGenerationData :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    CofibrantGenerationData Actual.SymmetricCarrier.{u, v} realizedGeneratorCardinal.{v} := by
  let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
  exact
    { I := NativeK.levelI (I := symmetricIndex)
      J := NativeK.generators symmetricFamily
      I_smallObject := Native.generatorsI_isCardinalForSmallObjectArgument
      J_smallObject := NativeK.generators_isCardinalForSmallObjectArgument symmetricFamily
      I_rlp := symmetric_five_classes.2.2.2.2.symm
      J_rlp := symmetric_five_classes.2.2.1.symm }




/-- Both actual stable factor records retain the original native construction. -/
def symmetricCofibrantFactorizationData :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    FunctorialFactorizationData (cofibrations Actual.SymmetricCarrier.{u, v})
      (trivialFibrations Actual.SymmetricCarrier.{u, v}) := by
  let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
  exact StableFactorization.cofibrantFactorizationData symmetricFamily

/-- The stable fibration factor retains the entire original paired K factor. -/
def symmetricFibrantFactorizationData :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    FunctorialFactorizationData (trivialCofibrations Actual.SymmetricCarrier.{u, v})
      (fibrations Actual.SymmetricCarrier.{u, v}) := by
  let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
  exact StableFactorization.fibrantFactorizationData symmetricFamily
    PointedCGWH.SymmetricOperatorHom.nativeSymmetricOperatorHom_isCofibrant

/-- Both full original middle functors and all four natural factor arrows are unchanged. -/
theorem symmetricFactorizationData_original :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    symmetricCofibrantFactorizationData.Z =
        (Native.cofibrantFactorizationData (B := B) (A := symmetricIndex)).Z ∧
      symmetricCofibrantFactorizationData.i =
        (Native.cofibrantFactorizationData (B := B) (A := symmetricIndex)).i ∧
      symmetricCofibrantFactorizationData.p =
        (Native.cofibrantFactorizationData (B := B) (A := symmetricIndex)).p ∧
      symmetricFibrantFactorizationData.Z = (NativeK.factorizationData symmetricFamily).Z ∧
      symmetricFibrantFactorizationData.i = (NativeK.factorizationData symmetricFamily).i ∧
      symmetricFibrantFactorizationData.p = (NativeK.factorizationData symmetricFamily).p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The original zero-arrow families and retained factors construct both stable replacements. -/
def symmetricCofibrantReplacement : Actual.SymmetricCarrier.{u, v} ⥤ Actual.SymmetricCarrier.{u, v} :=
  Diagrams.fromZeroArrow ⋙ symmetricCofibrantFactorizationData.Z

/-- The entire original zero-target Arrow family is composed with the original K middle functor. -/
def symmetricFibrantReplacement : Actual.SymmetricCarrier.{u, v} ⥤ Actual.SymmetricCarrier.{u, v} :=
  Diagrams.toZeroArrow ⋙ symmetricFibrantFactorizationData.Z

/-- The full replacement projection is the original I right-factor transformation. -/
def symmetricCofibrantReplacementCounit :
    symmetricCofibrantReplacement ⟶ 𝟭 Actual.SymmetricCarrier.{u, v} :=
  Functor.whiskerLeft Diagrams.fromZeroArrow symmetricCofibrantFactorizationData.p

/-- The full replacement unit is the original paired K left-factor transformation. -/
def symmetricFibrantReplacementUnit :
    𝟭 Actual.SymmetricCarrier.{u, v} ⟶ symmetricFibrantReplacement :=
  Functor.whiskerLeft Diagrams.toZeroArrow symmetricFibrantFactorizationData.i

/-- Both complete replacement functors are the original native Q and paired Omega replacement. -/
theorem symmetricReplacement_original :
    symmetricCofibrantReplacement =
        Replacement.cofibrantReplacement (B := B) (A := symmetricIndex) ∧
      symmetricFibrantReplacement = NativeK.omegaReplacement symmetricFamily ∧
      symmetricCofibrantReplacementCounit =
        Replacement.cofibrantReplacementCounit (B := B) (A := symmetricIndex) ∧
      symmetricFibrantReplacementUnit = NativeK.omegaReplacementUnit symmetricFamily :=
  ⟨rfl, rfl, rfl, rfl⟩



/-- The identity compares the original level and this actual stable value. -/
def symmetricLevelToStableAdjunction :
    ExplicitModelIdentity.comparison
        (Native.modelCategory (B := B) (A := symmetricIndex)) symmetricModelCategory ⊣
      ExplicitModelIdentity.comparison symmetricModelCategory
        (Native.modelCategory (B := B) (A := symmetricIndex)) :=
  ExplicitModelIdentity.identityAdjunction
    (Native.modelCategory (B := B) (A := symmetricIndex)) symmetricModelCategory

/-- Actual cofibration equality and native level weakness give the identity Quillen pair. -/
theorem symmetricLevelToStableAdjunction_isQuillen :
    symmetricLevelToStableAdjunction.IsQuillenAdjunction :=
  ExplicitModelIdentity.identityAdjunction_isQuillen
    (Native.modelCategory (B := B) (A := symmetricIndex)) symmetricModelCategory
    Native.cofibrations_eq (NativeK.levelWeak_le_omegaTests symmetricFamily)

/-- The two stable weak factorization systems use those exact original factor records. -/
theorem symmetric_functorialFactorizations :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    HasFunctorialFactorization (cofibrations Actual.SymmetricCarrier.{u, v})
        (trivialFibrations Actual.SymmetricCarrier.{u, v}) ∧
      HasFunctorialFactorization (trivialCofibrations Actual.SymmetricCarrier.{u, v})
        (fibrations Actual.SymmetricCarrier.{u, v}) :=
  ⟨⟨⟨symmetricCofibrantFactorizationData⟩⟩, ⟨⟨symmetricFibrantFactorizationData⟩⟩⟩

/-- All actual stable cofibrations are the unchanged native projective cofibrations. -/
theorem symmetric_cofibrations_eq_level :
    symmetricModelCategory.{u, v}.categoryWithCofibrations.cofibrations =
      (Native.modelCategory (B := B) (A := symmetricIndex)).categoryWithCofibrations.cofibrations := by
  change (NativeK.levelI (I := symmetricIndex)).rlp.llp = _
  exact (Native.cofibrations_eq (B := B) (A := symmetricIndex)).symm

/-- The complete original I left leg keeps the same native zero source. -/
def symmetricInitialToQ :
    (Functor.const Actual.SymmetricCarrier.{u, v}).obj Diagrams.zeroDiagram ⟶
      symmetricCofibrantReplacement :=
  Functor.whiskerLeft Diagrams.fromZeroArrow symmetricCofibrantFactorizationData.i

/-- The complete original K right leg keeps the same native zero target. -/
def symmetricRToZero : symmetricFibrantReplacement ⟶
    (Functor.const Actual.SymmetricCarrier.{u, v}).obj Diagrams.zeroDiagram :=
  Functor.whiskerLeft Diagrams.toZeroArrow symmetricFibrantFactorizationData.p

/-- Both remaining entire replacement arrows retain the actual native I and K values. -/
theorem symmetricReplacement_zero_legs :
    symmetricInitialToQ = Replacement.initialToCofibrantReplacement
        (B := B) (A := symmetricIndex) ∧
      symmetricRToZero = Functor.whiskerLeft Diagrams.toZeroArrow
        (NativeK.factorizationData symmetricFamily).p := ⟨rfl, rfl⟩

/-- The actual original I output is cofibrant in this same stable model. -/
theorem symmetricQ_isCofibrant (X : Actual.SymmetricCarrier.{u, v}) :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    IsCofibrant (symmetricCofibrantReplacement.obj X) := by
  let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
  change IsCofibrant (symmetricCofibrantReplacement.obj X)
  rw [isCofibrant_iff_of_isInitial (symmetricInitialToQ.app X) Diagrams.zeroDiagramIsInitial]
  exact (cofibration_iff (symmetricInitialToQ.app X)).mpr
    (symmetricCofibrantFactorizationData.hi (Diagrams.fromZeroArrow.obj X))

/-- The actual original I counit is a stable trivial fibration at every input. -/
theorem symmetricQCounit_trivialFibration (X : Actual.SymmetricCarrier.{u, v}) :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    trivialFibrations Actual.SymmetricCarrier.{u, v}
      (symmetricCofibrantReplacementCounit.app X) :=
  symmetricCofibrantFactorizationData.hp (Diagrams.fromZeroArrow.obj X)

/-- The original full-family K output is fibrant in this exact stable model. -/
theorem symmetricR_isFibrant (X : Actual.SymmetricCarrier.{u, v}) :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    IsFibrant (symmetricFibrantReplacement.obj X) := by
  let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
  change IsFibrant (symmetricFibrantReplacement.obj X)
  exact (symmetric_isFibrant_iff_isOmega _).mpr
    (NativeK.omegaReplacement_isOmega symmetricFamily X)

/-- The actual original K unit is a stable trivial cofibration at every input. -/
theorem symmetricRUnit_trivialCofibration (X : Actual.SymmetricCarrier.{u, v}) :
    let : ModelCategory Actual.SymmetricCarrier.{u, v} := symmetricModelCategory
    trivialCofibrations Actual.SymmetricCarrier.{u, v}
      (symmetricFibrantReplacementUnit.app X) :=
  symmetricFibrantFactorizationData.hi (Diagrams.toZeroArrow.obj X)

/-- Both actual replacement factors give the original zero-arrow equations. -/
theorem symmetric_replacement_fac (X : Actual.SymmetricCarrier.{u, v}) :
    symmetricInitialToQ.app X ≫ symmetricCofibrantReplacementCounit.app X = Diagrams.zeroTo X ∧
      symmetricFibrantReplacementUnit.app X ≫ symmetricRToZero.app X = Diagrams.toZero X :=
  ⟨symmetricCofibrantFactorizationData.fac_app, symmetricFibrantFactorizationData.fac_app⟩

/-- Both original full replacement functors retain every original input-arrow square. -/
theorem symmetric_replacement_naturality {X Y : Actual.SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    symmetricCofibrantReplacement.map f ≫ symmetricCofibrantReplacementCounit.app Y =
        symmetricCofibrantReplacementCounit.app X ≫ f ∧
      f ≫ symmetricFibrantReplacementUnit.app Y =
        symmetricFibrantReplacementUnit.app X ≫ symmetricFibrantReplacement.map f :=
  ⟨symmetricCofibrantReplacementCounit.naturality f, symmetricFibrantReplacementUnit.naturality f⟩

end HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

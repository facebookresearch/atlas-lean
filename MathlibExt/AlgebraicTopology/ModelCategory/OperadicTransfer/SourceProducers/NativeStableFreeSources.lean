/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.SourceProducers.NativeClosedSources
import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.SourceProducers.ContinuousSources
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableModelConstruction

/-!
# Actual native stable free-I/free-J source producers

The source category is bound to the already constructed native symmetric stable
model. Its original I is the entire native free-boundary family and its original
J is the entire original horn plus correlated boundary/mapping-cylinder K bank.
The stable cofibrations equal the original level cofibrations; closedness is
therefore derived on the very same coefficient-orbit cell class.

The original I endpoint Hom comparison is rank-free on closed ordinal diagrams.
The full J bank uses the existing bounded scalar/cylinder source proof at exactly
the realized-generator cardinal, with the original caller bottom and continuous
histories. The actual color/free-algebra adjunction then produces both original
free-I/free-J small-object arguments. No compactness of a general bounded
coefficient or replacement of the original stable J family is asserted.

These are source-smallness producers. Positive stable symmetric h-monoidality
and the positive R-module carrier remain the separate positive source lane.
-/

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory Limits MorphismProperty MonoidalCategory Opposite
open CategoryTheory.Operad CategoryTheory.Operad.Tensor
open CategoryTheory.EnrichedFunctorCat
open CategoryTheory.OperadicOrbitCells
open CategoryTheory.SmallObject.CellularNormalization
open HomotopicalAlgebra PointedCGWH
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory

namespace HomotopicalAlgebra.OperadicTransfer.SourceProducers.NativeStableFreeSources

/-- The literal original native symmetric carrier. -/
abbrev Carrier := NativeClosedSources.Carrier.{u, v}

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The original chosen native symmetric stable model. -/
local instance chosenStableModel : ModelCategory Carrier.{u, v} :=
  EnrichedProjective.Native.StableModelConstruction.symmetricModelCategory

local instance baseNativeLimits : HasLimitsOfSize.{v, v} CGWH.{u, v} :=
  CGWH.limits.instHasLimitsOfSize

local instance basePointedLimits : HasLimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  change HasLimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

local instance basePointedColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} :=
  EnrichedProjective.Native.nativeColimits

/-- The finite tensor induced by the original native binary symmetric tensor. -/
local instance literalFiniteTensor : FiniteTensor Carrier.{u, v} := FiniteTensor.ofSymmetric _

local instance literalTensorSlots :
    FiniteTensorPreservesColimitsInEachSlot.{v, v + 1, v} Carrier.{u, v} :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot _

/-- Bind the actual native stable model, tensor, closed structure and original
small color palette to the source context consumed by the operadic transfer. -/
def sourceContext (W : Type w) [Small.{v} W] : SourceContext.{w, v, v + 1, v} where
  C := Carrier.{u, v}
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  closed := inferInstance
  model := EnrichedProjective.Native.StableModelConstruction.symmetricModelCategory
  complete := by
    exact EnrichedFunctorCat.hasLimitsOfSize (V := PointedCGWH.{u, v})
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
  cocomplete := by
    exact EnrichedFunctorCat.hasColimitsOfSize (V := PointedCGWH.{u, v})
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
  W := W
  smallColors := inferInstance

/-- The original native stable generating cofibrations are retained literally. -/
abbrev originalI : MorphismProperty Carrier.{u, v} :=
  NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The entire original stable J bank, including both original correlated labels. -/
abbrev originalJ : MorphismProperty Carrier.{u, v} :=
  NativeK.generators Actual.symmetricFamily.{u, v}

variable (W : Type w) [Small.{v} W]

/-- The finite tensor of the same original chosen source context. -/
local instance actualFiniteTensor : FiniteTensor (sourceContext.{u, v} W).C :=
  (sourceContext.{u, v} W).finiteTensor

local instance actualProfileColimits (d : W) :
    HasColimitsOfShape (AnalyticIndex W d) (sourceContext.{u, v} W).C :=
  (sourceContext.{u, v} W).profileColimits d

/-- The selected stable source has exactly the original level cofibrations. -/
theorem sourceCofibrations_eq :
    cofibrations (sourceContext.{u, v} W).C =
      @cofibrations Carrier.{u, v} inferInstance
        (EnrichedProjective.Native.modelCategory (B := B)).categoryWithCofibrations := by
  change
    @cofibrations Carrier.{u, v} inferInstance
        EnrichedProjective.Native.StableModelConstruction.symmetricModelCategory.categoryWithCofibrations = _
  exact EnrichedProjective.Native.StableModelConstruction.symmetric_five_classes.2.1.trans
    EnrichedProjective.Native.cofibrations_eq.symm

/-- The full arbitrary-coefficient cell class is closed for the selected
actual stable model, using its earned original cofibration equality. -/
theorem sourceCofibrationCellsClosed :
    OperadicAcyclicCells.cofibrationCells.{v, v} (sourceContext.{u, v} W).C ≤
      NativeClosedSources.closedInclusions.{u, v} := by
  change cellularClosure.{v, v} (orbitGenerators (cofibrations (sourceContext.{u, v} W).C)) ≤ _
  rw [sourceCofibrations_eq W]
  exact NativeClosedSources.originalCofibrationCellsClosed

/-- Both original I endpoints preserve the actual selected stable
cofibration-cell diagrams, including every latching prefix and endpoint. -/
theorem originalISourceHom :
    SourceHomPreservation.{v + 1, v, v} originalI.{u, v}
      (OperadicAcyclicCells.cofibrationCells.{v, v} (sourceContext.{u, v} W).C) where
  domains i := by
    intro T _ _ _ D hD
    exact (NativeClosedSources.originalGeneratorSourceHomClosed
      CGWH.realizedBoundaryInclusions le_sup_left).domains i T D
        (fun a b f => sourceCofibrationCellsClosed W _ (hD a b f))
  codomains i := by
    intro T _ _ _ D hD
    exact (NativeClosedSources.originalGeneratorSourceHomClosed
      CGWH.realizedBoundaryInclusions le_sup_left).codomains i T D
        (fun a b f => sourceCofibrationCellsClosed W _ (hD a b f))

/-- The full original stable J source theorem is applied at the original
realized cardinal and bottom, after deriving actual closed transitions. -/
theorem originalJContinuousSources :
    SourcesPreserveContinuousColimits (sourceContext.{u, v} W) originalJ.{u, v}
      (OperadicAcyclicCells.cofibrationCells.{v, v} (sourceContext.{u, v} W).C)
      realizedGeneratorCardinal.{v} := by
  intro X Y i hi D hContinuous hD
  let : D.IsWellOrderContinuous := hContinuous
  let : (show realizedGeneratorCardinal.{v}.ord.ToType ⥤ Carrier.{u, v} from D).IsWellOrderContinuous :=
    hContinuous
  exact NativeK.generatorsSource_preservesClosedColimit Actual.symmetricFamily.{u, v} i hi D
    (fun a {_ _} f => sourceCofibrationCellsClosed W _ (hD _ _ f) a)

/-- The chosen source's original I lifting equation is the original
stable model's complete generating equation. -/
theorem originalI_rlp : originalI.{u, v}.rlp = trivialFibrations (sourceContext.{u, v} W).C :=
  EnrichedProjective.Native.StableModelConstruction.symmetricGenerationData.I_rlp

/-- The entire original horn/K union detects exactly the selected stable fibrations. -/
theorem originalJ_rlp : originalJ.{u, v}.rlp = fibrations (sourceContext.{u, v} W).C :=
  EnrichedProjective.Native.StableModelConstruction.symmetricGenerationData.J_rlp

variable (O : ColoredOperadObj W (sourceContext.{u, v} W).C)

/-- The category of algebras over the original source operad. -/
local instance actualAlgebraCategory : Category (Algebra O) := inferInstance

local instance originalRankRegular : Fact realizedGeneratorCardinal.{v}.IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal⟩

/-- The actual free-I source smallness is produced from both original I
endpoint Hom comparisons on the same full free-cell histories. -/
theorem actualFreeISourceSmallness :
    ActualFreeCellSourceSmallness (sourceContext.{u, v} W) O originalI.{u, v}
      realizedGeneratorCardinal.{v} :=
  actualFreeCellSourceSmallness (sourceContext.{u, v} W) O originalI.{u, v}
    (SemiModel.ColorSource.originalIGenerators_le_cofibrations _ _ (originalI_rlp W))
    (originalISourceHom.{u, v} W) realizedGeneratorCardinal.{v}

/-- The actual free-J source smallness uses the full original stable J
bank and its precise continuous original-cardinal source theorem. -/
theorem actualFreeJSourceSmallness :
    ActualFreeCellSourceSmallness (sourceContext.{u, v} W) O originalJ.{u, v}
      realizedGeneratorCardinal.{v} :=
  actualFreeCellSourceSmallnessOfContinuousSources (sourceContext.{u, v} W) O originalJ.{u, v}
    ((SemiModel.ColorSource.originalJGenerators_le_trivialCofibrations _ _
      (originalJ_rlp.{u, v} W)).trans inf_le_left) realizedGeneratorCardinal.{v}
    (originalJContinuousSources.{u, v} W)

set_option backward.isDefEq.respectTransparency false in
/-- All six actual free-I small-object fields at the original native rank. -/
theorem actualFreeI_smallObject :
    (freeGenerators (sourceContext.{u, v} W) O originalI.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := by
  let : Fact realizedGeneratorCardinal.{v}.IsRegular := ⟨isRegular_realizedGeneratorCardinal⟩
  let : originalI.{u, v}.IsSmall.{v} :=
    EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument.isSmall
  exact freeGenerators_smallObject (sourceContext.{u, v} W) O originalI.{u, v}
    (SemiModel.ColorSource.originalIGenerators_le_cofibrations _ _ (originalI_rlp W))
    (originalISourceHom.{u, v} W) realizedGeneratorCardinal.{v}

set_option backward.isDefEq.respectTransparency false in
/-- The full original stable free-J small-object argument uses the same
native rank and caller bottom, without a rank-free J compactness premise. -/
theorem actualFreeJ_smallObject :
    (freeGenerators (sourceContext.{u, v} W) O originalJ.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := by
  let : Fact realizedGeneratorCardinal.{v}.IsRegular := ⟨isRegular_realizedGeneratorCardinal⟩
  let : originalJ.{u, v}.IsSmall.{v} := NativeK.generators_isSmall Actual.symmetricFamily.{u, v}
  exact freeGeneratorsSmallObjectOfContinuousSources (sourceContext.{u, v} W) O originalJ.{u, v}
    ((SemiModel.ColorSource.originalJGenerators_le_trivialCofibrations _ _
      (originalJ_rlp.{u, v} W)).trans inf_le_left) realizedGeneratorCardinal.{v}
    (originalJContinuousSources.{u, v} W)


end HomotopicalAlgebra.OperadicTransfer.SourceProducers.NativeStableFreeSources

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberNullity
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses
import MathlibExt.AlgebraicTopology.Spectra.Sequential.KOmegaRecognition

/-!
# Stable models from the original native generator and fiber arguments

The original sequential K-right Omega-test equivalence has an actual
Omega-test-null chosen fiber. The native one-sphere recognition theorem
therefore proves the all-arrow right-class equality. The original I and K
factor records and all-source K-left acyclicity then construct the stable
model on the unchanged continuous enriched spectrum carrier.

The model retains the original realized-generator cardinal, every caller
bottom, both entire small-object factor records, and the full original
Omega-target Hom-test weak class. No stable model, class equality, or
factorization result is a supplied native hypothesis.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory ZeroObject

namespace HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

open OperatorStabilizationK

private abbrev sequentialIndex := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev sequentialFamily :=
  PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private instance sequentialFiniteLimits : HasFiniteLimits PointedCGWH.SequentialSpectrum.{u, v} :=
  (Native.modelCategory (B := B) (A := sequentialIndex)).cm1a

private instance sequentialFiniteColimits :
    HasFiniteColimits PointedCGWH.SequentialSpectrum.{u, v} :=
  (Native.modelCategory (B := B) (A := sequentialIndex)).cm1b

/-- Original K-rightness and the full Omega Hom tests give precisely the
original level-I right class, on arbitrary sequential endpoints. -/
theorem sequential_right_class_eq :
    (NativeK.levelI (I := sequentialIndex.{u, v})).rlp =
      (NativeK.generators sequentialFamily).rlp ⊓ NativeK.omegaTests sequentialFamily := by
  apply le_antisymm (NativeK.levelI_right_le_KRight_omegaTests sequentialFamily)
  intro X Y p hp
  let c := PullbackCone.mk (pullback.fst p (Diagrams.zeroTo Y))
    (pullback.snd p (Diagrams.zeroTo Y)) (by exact pullback.condition)
  have hc : IsLimit c := pullbackIsPullback p (Diagrams.zeroTo Y)
  have hFiber := NativeK.OriginalFiberNullity.sequentialChosenFiberCollapse_omegaTests
    (B := B) p hp.1 hp.2 c hc
  have hpK : PointedCGWH.SequentialSpectrum.StableK.generators.rlp p := by
    simpa only [PointedCGWH.SequentialSpectrum.StabilizationKAdapter.generators_eq] using hp.1
  have hLevel := PointedCGWH.SequentialSpectrum.StableK.chosenFiber_omegaTests_levelTrivialFibration
    (B := B) p hpK c hc hFiber
  exact Native.Data.generatorsI_rlp.ge p hLevel.1

/-- The original K factor of each arrow derives the full trivial-left
class from its actual I and Omega-test classes. -/
theorem sequential_left_class_eq :
    (NativeK.generators sequentialFamily.{u, v}).rlp.llp =
      (NativeK.levelI (I := sequentialIndex)).rlp.llp ⊓ NativeK.omegaTests sequentialFamily :=
  OriginalGeneratedModel.left_class_eq
    (NativeK.levelI (I := sequentialIndex)) (NativeK.generators sequentialFamily)
    (NativeK.omegaTests sequentialFamily) inferInstance sequential_right_class_eq
    PointedCGWH.Spectra.NativeStable.sequentialKLeft_le_omegaTests
    (NativeK.factorizationData sequentialFamily)

/-- The native sequential stable model is constructed from the original
I/K records and the proved full right and left recognition laws. -/
@[instance_reducible]
def sequentialModelCategory : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
  OriginalGeneratedModel.modelCategory
    (NativeK.levelI (I := sequentialIndex)) (NativeK.generators sequentialFamily)
    (NativeK.omegaTests sequentialFamily) inferInstance sequential_right_class_eq
    PointedCGWH.Spectra.NativeStable.sequentialKLeft_le_omegaTests
    (OriginalFactorizationAssembly.originalI (B := B) (A := sequentialIndex))
    (NativeK.factorizationData sequentialFamily)

/-- All five classes belong to this single native sequential stable model
and retain the entire original I/K families and Omega-target Hom tests. -/
theorem sequential_five_classes :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} = NativeK.omegaTests sequentialFamily ∧
      cofibrations PointedCGWH.SequentialSpectrum.{u, v} =
        (NativeK.levelI (I := sequentialIndex)).rlp.llp ∧
      fibrations PointedCGWH.SequentialSpectrum.{u, v} = (NativeK.generators sequentialFamily).rlp ∧
      trivialCofibrations PointedCGWH.SequentialSpectrum.{u, v} =
        (NativeK.generators sequentialFamily).rlp.llp ∧
      trivialFibrations PointedCGWH.SequentialSpectrum.{u, v} =
        (NativeK.levelI (I := sequentialIndex)).rlp :=
  OriginalGeneratedModel.five_classes
    (NativeK.levelI (I := sequentialIndex)) (NativeK.generators sequentialFamily)
    (NativeK.omegaTests sequentialFamily) inferInstance sequential_right_class_eq
    PointedCGWH.Spectra.NativeStable.sequentialKLeft_le_omegaTests
    (OriginalFactorizationAssembly.originalI (B := B) (A := sequentialIndex))
    (NativeK.factorizationData sequentialFamily)

/-- The constructed stable fibrant objects are exactly the full original
sequential Omega objects, using their actual map to the original zero. -/
theorem sequential_isFibrant_iff_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    IsFibrant X ↔ NativeK.IsOmega sequentialFamily X := by
  let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
  change IsFibrant X ↔ NativeK.IsOmega sequentialFamily X
  rw [isFibrant_iff_of_isTerminal (Diagrams.toZero X) Diagrams.zeroDiagramIsTerminal]
  rw [fibration_iff, sequential_five_classes.2.2.1]
  exact NativeK.lifting_toZero_iff_isOmega sequentialFamily X

/-- The stable model is generated by the entire original free boundary
family and correlated K family at the unchanged native cardinal and bottom. -/
def sequentialGenerationData :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    CofibrantGenerationData PointedCGWH.SequentialSpectrum.{u, v}
      realizedGeneratorCardinal.{v} := by
  let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
  exact
    { I := NativeK.levelI (I := sequentialIndex)
      J := NativeK.generators sequentialFamily
      I_smallObject := Native.generatorsI_isCardinalForSmallObjectArgument
      J_smallObject := NativeK.generators_isCardinalForSmallObjectArgument sequentialFamily
      I_rlp := sequential_five_classes.2.2.2.2.symm
      J_rlp := sequential_five_classes.2.2.1.symm }

end HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

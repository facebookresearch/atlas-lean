/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableFactorizations

/-!
# Original classes and factor choices for native orthogonal stabilization

All classes are on the unchanged full continuous orthogonal carrier. The
weak class uses every actual native Omega target in the original level Ho.
Cofibrations use the original free I cells, and fibrations use the entire
original correlated K family. Both original lifting-class WFS and both
classified factor records retain the original realized cardinal and bottom.

The all-arrow recognition theorem is needed to identify the intersections
as the original I-right and K-left classes in the stable model. The class
definitions and original source algorithms here use no stable model input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

/-- The entire original continuous free boundary family is retained. -/
abbrev originalI : MorphismProperty C.{u, v} := NativeK.levelI (I := O.{u, v})

/-- The whole original paired K family retains every source, added degree
and original boundary/cylinder label. -/
abbrev originalK : MorphismProperty C.{u, v} := NativeK.generators orthogonalFamily

/-- The original free I lifting class is the ordinary cofibration class. -/
abbrev stableCofibrations : MorphismProperty C.{u, v} := originalI.rlp.llp

/-- The entire original K lifting class is the stable fibration class. -/
abbrev stableFibrations : MorphismProperty C.{u, v} := originalK.rlp

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
  NativeK.generators_isCardinalForSmallObjectArgument

/-- Every original native Omega target tests the same level Ho source map. -/
abbrev stableWeakEquivalences : MorphismProperty C.{u, v} := NativeK.omegaTests orthogonalFamily

/-- The full trivial-cofibration intersection uses the same original
cofibrations and actual all-target weak tests. -/
abbrev stableTrivialCofibrations : MorphismProperty C.{u, v} :=
  stableCofibrations ⊓ stableWeakEquivalences

/-- The full trivial-fibration intersection uses the entire original
paired right class and same actual weak tests. -/
abbrev stableTrivialFibrations : MorphismProperty C.{u, v} :=
  stableFibrations ⊓ stableWeakEquivalences

instance stableWeakEquivalences_containsIdentities :
    stableWeakEquivalences.{u, v}.ContainsIdentities := inferInstance

instance stableWeakEquivalences_twoOutOfThree :
    stableWeakEquivalences.{u, v}.HasTwoOutOfThreeProperty := inferInstance

instance stableWeakEquivalences_retracts :
    stableWeakEquivalences.{u, v}.IsStableUnderRetracts := inferInstance

/-- The weak tests retain every entire original native Omega-target Hom
function, with no locality assumption on either source endpoint. -/
theorem stableWeakEquivalences_iff {X Y : C.{u, v}} (f : X ⟶ Y) :
    stableWeakEquivalences f ↔ ∀ E : C.{u, v}, NativeK.IsOmega orthogonalFamily E →
      Function.Bijective (fun g : (toHomotopyCategory C.{u, v}).obj Y ⟶
        (toHomotopyCategory C.{u, v}).obj E => (toHomotopyCategory C.{u, v}).map f ≫ g) := Iff.rfl

/-- Every full paired mapping corner remains part of the original
fibration recognition test. -/
theorem stableFibrations_iff {X Y : C.{u, v}} (p : X ⟶ Y) :
    stableFibrations p ↔ fibrations C.{u, v} p ∧ ∀ l : ℕ × ℕ,
      trivialFibrations PointedCGWH.{u, v}
        (PointedCGWH.NativeMappingCorner.square (NativeK.cylinderSource orthogonalFamily l) p).π :=
  NativeK.lifting_iff orthogonalFamily p

/-- These exact cofibrations are the original ordinary native level class. -/
theorem stableCofibrations_eq_level : stableCofibrations.{u, v} = cofibrations C.{u, v} :=
  (HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq
    (B := B) (A := O.{u, v})).symm

/-- All native level weak maps retain their same full stable Hom tests. -/
theorem levelWeak_le_stableWeakEquivalences :
    weakEquivalences C.{u, v} ≤ stableWeakEquivalences :=
  NativeK.levelWeak_le_omegaTests orthogonalFamily

/-- The original I-right arrows belong to the full trivial-right
intersection on arbitrary native endpoints. -/
theorem originalIRight_le_stableTrivialFibrations :
    originalI.{u, v}.rlp ≤ stableTrivialFibrations :=
  NativeK.levelI_right_le_KRight_omegaTests orthogonalFamily

/-- The existing Thom-Hom cell proof makes the entire original K-left
class acyclic in the actual all-target tests. -/
theorem originalKLeft_le_stableWeakEquivalences :
    originalK.{u, v}.rlp.llp ≤ stableWeakEquivalences :=
  PointedCGWH.Spectra.NativeStable.orthogonalKLeft_le_omegaTests

/-- All full paired K-left maps belong to the original trivial-left
intersection, by the unchanged source Hom cell proof. -/
theorem originalKLeft_le_stableTrivialCofibrations :
    originalK.{u, v}.rlp.llp ≤ stableTrivialCofibrations := by
  change originalK.rlp.llp ≤ stableCofibrations ⊓ stableWeakEquivalences
  rw [stableCofibrations_eq_level]
  exact NativeK.left_le_levelCofibrations_and_omegaTests orthogonalFamily
    PointedCGWH.Spectra.NativeStable.orthogonalHom_isCofibrant

/-- Cofibrations are exactly retracts of original free I cells of the
same original realized-cardinal shape. -/
theorem stableCofibrations_eq_retractCells :
    stableCofibrations.{u, v} =
      ((coproducts.{v} originalI).pushouts.transfiniteCompositionsOfShape
        realizedGeneratorCardinal.{v}.ord.ToType).retracts :=
  SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' originalI realizedGeneratorCardinal

/-- The entire paired K-left closure uses the same original source
cells, original realized cardinal and caller's ordinal bottom. -/
theorem originalKLeft_eq_retractCells :
    originalK.{u, v}.rlp.llp =
      ((coproducts.{v} originalK).pushouts.transfiniteCompositionsOfShape
        realizedGeneratorCardinal.{v}.ord.ToType).retracts :=
  SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' originalK realizedGeneratorCardinal

/-- The original I record is retained before recognition of its stable
trivial-right membership. -/
abbrev originalIFactorizationData : FunctorialFactorizationData
    stableCofibrations.{u, v} originalI.rlp :=
  OriginalFactorizationAssembly.originalI (B := B) (A := O.{u, v})

/-- The entire original paired K record is retained before recognizing
its full stable trivial-left membership. -/
abbrev originalKFactorizationData : FunctorialFactorizationData
    originalK.{u, v}.rlp.llp stableFibrations :=
  NativeK.factorizationData orthogonalFamily

/-- The original I algorithm supplies its whole actual lifting-class WFS. -/
theorem originalI_wfs : IsWeakFactorizationSystem stableCofibrations.{u, v} originalI.rlp :=
  OriginalGeneratedModel.weakFactorizationSystemOfGiven originalI originalIFactorizationData

/-- The same paired K algorithm supplies its entire actual lifting-class WFS. -/
theorem originalK_wfs : IsWeakFactorizationSystem originalK.{u, v}.rlp.llp stableFibrations :=
  OriginalGeneratedModel.weakFactorizationSystemOfGiven originalK originalKFactorizationData

/-- The full I record in the candidate model intersections is the
existing first orthogonal record of the original six algorithms. -/
abbrev classifiedIFactorizationData : FunctorialFactorizationData
    stableCofibrations.{u, v} stableTrivialFibrations :=
  PointedCGWH.Spectra.NativeStable.orthogonalIFactorizationData

/-- The full K record in the candidate model intersections is the
existing paired orthogonal record, classified by actual Thom cells. -/
abbrev classifiedKFactorizationData : FunctorialFactorizationData
    stableTrivialCofibrations.{u, v} stableFibrations :=
  PointedCGWH.Spectra.NativeStable.orthogonalKFactorizationData

/-- Both classified middle functors and all four natural maps are the
exact entire original I and K values. -/
theorem classifiedFactorization_original_fields :
    classifiedIFactorizationData.{u, v}.Z = originalIFactorizationData.Z ∧
      classifiedIFactorizationData.{u, v}.i = originalIFactorizationData.i ∧
      classifiedIFactorizationData.{u, v}.p = originalIFactorizationData.p ∧
      classifiedKFactorizationData.{u, v}.Z = originalKFactorizationData.Z ∧
      classifiedKFactorizationData.{u, v}.i = originalKFactorizationData.i ∧
      classifiedKFactorizationData.{u, v}.p = originalKFactorizationData.p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end PointedCGWH.Spectra.Orthogonal.NativeStableModels

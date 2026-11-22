/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.SourceHomTransfer
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.UnaryTensorOrbit
import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer.OriginalRank
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.NativeSources
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.WeakScalarDerived
import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.SourceProducers.NativeStableFreeSources

/-!
# Original-rank native module sources

The original native base source Hom theorems are transported through the
actual free-module/forget adjunction and the whole original module cell
diagram. Arbitrary scalar tensors enter the full native coefficient-orbit
cell class through its actual unary coefficient Arrow isomorphism. The
original full K source bank is used only at its original cardinal and bottom.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty CategoryTheory.SmallObject HomotopicalAlgebra
open CategoryTheory.OperadicOrbitCells
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.NativeOriginalRankSources.Symmetric

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

private abbrev C := Actual.SymmetricCarrier.{u, v}
private abbrev I : MorphismProperty C.{u, v} :=
  NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev J : MorphismProperty C.{u, v} := NativeK.generators Actual.symmetricFamily.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

/-- The original symmetric stable model at the retained realized-generator ordinal bottom. -/
local instance originalStableModel : ModelCategory C.{u, v} :=
  StableModelConstruction.symmetricModelCategory (B := B)

private abbrev Q : MorphismProperty C.{u, v} := OperadicAcyclicCells.cofibrationCells.{v, v} C.{u, v}

local instance originalColimits : HasColimitsOfSize.{v, v} C.{u, v} :=
  (OperadicTransfer.SourceProducers.NativeStableFreeSources.sourceContext.{u, v} PUnit).cocomplete

local instance originalIEligibility : I.{u, v}.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
    (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
local instance originalJEligibility : J.{u, v}.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  NativeK.generators_isCardinalForSmallObjectArgument Actual.symmetricFamily.{u, v}

local instance originalLocallySmall : LocallySmall.{v} C.{u, v} :=
  SmallObject.locallySmall I realizedGeneratorCardinal.{v}

local instance targetCoproducts : Q.{u, v}.IsStableUnderCoproducts.{v} :=
  OperadicAcyclicCells.cofibrationCells_stable.2.1
local instance targetCobase : Q.{u, v}.IsStableUnderCobaseChange :=
  OperadicAcyclicCells.cofibrationCells_stable.1
local instance targetTransfinite : Q.{u, v}.IsStableUnderTransfiniteComposition.{v} :=
  OperadicAcyclicCells.cofibrationCells_stable.2.2

local instance targetIso : Q.{u, v}.RespectsIso := by
  apply RespectsIso.of_respects_arrow_iso
  intro a b e ha
  obtain ⟨T, _, _, _, _, ⟨d⟩⟩ := (transfiniteCompositions_iff _ a.hom).mp ha
  exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ T b.hom ⟨d.ofArrowIso e⟩

private theorem orbit_le_target : orbitGenerators (cofibrations C.{u, v}) ≤ Q.{u, v} :=
  ((orbitGenerators (cofibrations C.{u, v})).le_coproducts.trans
    ((orbitGenerators (cofibrations C.{u, v})).coproducts.{v}).le_pushouts).trans
      ((orbitGenerators (cofibrations C.{u, v})).coproducts.{v}).pushouts.le_transfiniteCompositions

variable (A : C.{u, v}) [MonObj A]

local instance moduleColimits : HasColimitsOfSize.{v, v} (Mod C.{u, v} A) := Mod.hasColimits.{v} A
local instance forgetColimits : PreservesColimitsOfSize.{v, v} (Mod.forget (D := C.{u, v}) A) :=
  ModuleTransfer.leftForgetPreservesColimits (Mon.mk A)
local instance forgetFaithful : (Mod.forget (D := C.{u, v}) A).Faithful :=
  { map_injective := fun h => Mod.hom_ext _ _ h }
local instance moduleLocallySmall : LocallySmall.{v} (Mod C.{u, v} A) :=
  locallySmall_of_faithful (Mod.forget (D := C.{u, v}) A)

/-- Every original free-I map retains its arbitrary scalar tensor in the full native orbit-cell class. -/
theorem originalFreeI_image : I.strictMap (Mod.free A) ≤ Q.inverseImage (Mod.forget (D := C.{u, v}) A) := by
  intro X Y f hf
  cases hf with
  | @map K L i hi =>
    change Q (A ◁ i)
    have hC := I.le_llp_rlp i hi
    rw [(StableModelConstruction.symmetric_five_classes (B := B)).2.2.2.2.symm, trivialFibrations_llp] at hC
    exact UnaryTensorOrbit.tensor_mem (cofibrations C.{u, v}) Q orbit_le_target A i hC

/-- The full original K image is treated by the same actual scalar tensor and full source class. -/
theorem originalFreeJ_image : J.strictMap (Mod.free A) ≤ Q.inverseImage (Mod.forget (D := C.{u, v}) A) := by
  intro X Y f hf
  cases hf with
  | @map K L i hi =>
    change Q (A ◁ i)
    have hC := J.le_llp_rlp i hi
    rw [(StableModelConstruction.symmetric_five_classes (B := B)).2.2.1.symm, fibrations_llp] at hC
    exact UnaryTensorOrbit.tensor_mem (cofibrations C.{u, v}) Q orbit_le_target A i hC.1

/-- The original native free-I source Hom comparison gives all module eligibility fields at the same rank. -/
theorem originalFreeI_smallObject :
    (I.strictMap (Mod.free A)).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} := by
  let : I.IsSmall.{v} := SmallObject.isSmall I realizedGeneratorCardinal.{v}
  apply SourceHomTransfer.originalImageSmallObject (Mod.free A) (Mod.forget (D := C.{u, v}) A)
    (Mod.freeForgetAdjunction A) I Q realizedGeneratorCardinal.{v} (originalFreeI_image A)
  intro X Y i hi F _ hF
  exact (OperadicTransfer.SourceProducers.NativeStableFreeSources.originalISourceHom.{u, v} PUnit).domains
    ⟨Arrow.mk i, hi⟩ realizedGeneratorCardinal.{v}.ord.ToType F (fun _ _ f => hF f)

/-- The full original K source theorem supplies module eligibility without changing its cardinal or bottom. -/
theorem originalFreeJ_smallObject :
    (J.strictMap (Mod.free A)).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} := by
  let : J.IsSmall.{v} := SmallObject.isSmall J realizedGeneratorCardinal.{v}
  apply SourceHomTransfer.originalImageSmallObject (Mod.free A) (Mod.forget (D := C.{u, v}) A)
    (Mod.freeForgetAdjunction A) J Q realizedGeneratorCardinal.{v} (originalFreeJ_image A)
  intro X Y i hi F hContinuous hF
  let : F.IsWellOrderContinuous := hContinuous
  exact OperadicTransfer.SourceProducers.NativeStableFreeSources.originalJContinuousSources.{u, v}
    PUnit i hi F (fun _ _ f => hF f)

/-- Both proved native free-image algorithms construct the actual module model at the original rank. -/
def originalModuleTransfer :
    RightTransfer.OriginalRankModelTransfer (Mod.free A) (Mod.forget (D := C.{u, v}) A)
      I J realizedGeneratorCardinal.{v} := by
  let : HasLimitsOfSize.{v, v} C.{u, v} :=
    (OperadicTransfer.SourceProducers.NativeStableFreeSources.sourceContext.{u, v} PUnit).complete
  let : HasLimitsOfSize.{v, v} (Mod C.{u, v} A) := Mod.hasLimits.{v} A
  let : (I.strictMap (Mod.free A)).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    originalFreeI_smallObject A
  let : (J.strictMap (Mod.free A)).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    originalFreeJ_smallObject A
  let : MonoidAxiom.{v} C.{u, v} :=
    PointedCGWH.Spectra.Symmetric.OriginalMonoidAxiom.originalStableMonoidAxiom
  exact RightTransfer.originalRankModelTransfer (Mod.free A) (Mod.forget (D := C.{u, v}) A)
    I J realizedGeneratorCardinal.{v} (Mod.freeForgetAdjunction A)
    (StableModelConstruction.symmetric_five_classes (B := B)).2.2.2.2.symm
    (StableModelConstruction.symmetric_five_classes (B := B)).2.2.1.symm
    (ModuleTransfer.leftFreeJLeft_underlying_weak (Mon.mk A) J
      (StableModelConstruction.symmetric_five_classes (B := B)).2.2.1.symm realizedGeneratorCardinal.{v})

/-- The constructed native model has exactly the original free-I cofibrations. -/
theorem originalModuleCofibrations :
    letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
    cofibrations (Mod C.{u, v} A) = (I.strictMap (Mod.free A)).rlp.llp := by
  let : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
  rw [← (originalModuleTransfer A).generation_I,
    (originalModuleTransfer A).generation.I_rlp, trivialFibrations_llp]

/-- Actual original-rank native module cofibrancy earns full relative flatness without source-bound premises. -/
theorem originalModule_relativeFlat (M : Mod C.{u, v} A) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
    IsCofibrant M → ModuleTransfer.WeakScalar.RelativeFlat M := by
  let : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
  let : (I.strictMap (Mod.free A)).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    originalFreeI_smallObject A
  intro hM
  let : IsCofibrant M := hM
  intro N N' f hf
  exact ModuleTransfer.FreeCellFlatness.relativeFlat_of_original_freeICells I realizedGeneratorCardinal.{v}
    (originalModuleCofibrations A) PointedCGWH.EnrichedBasedHomotopyExtension.property
    (NativeSources.Symmetric.originalStableCellClosure (B := B))
    (NativeSources.Symmetric.originalI_coefficientFlatness (B := B))
    (fun N {K L} i hi => NativeSources.Symmetric.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi)
    M f hf

variable {A} {A' : C.{u, v}} [MonObj A']

/-- The actual balanced unit is weak in the completely source-derived native module model. -/
theorem originalScalarUnit_weak (p : A ⟶ A') [IsMonHom p]
    (hp : weakEquivalences C.{u, v} p) (M : Mod C.{u, v} A) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
    IsCofibrant M → WeakEquivalence ((Mod.ExtensionOfScalars.adjunction p).unit.app M) := by
  let : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
  intro hM
  exact ModuleTransfer.WeakScalar.scalarUnit_weak (originalModuleTransfer A).weak_eq p hp M
    (originalModule_relativeFlat A M hM)

/-- Original native I/K source algorithms earn the full scalar Quillen equivalence for arbitrary scalars. -/
theorem originalScalarQuillenEquivalence (p : A ⟶ A') [IsMonHom p]
    (hp : weakEquivalences C.{u, v} p) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
    letI : ModelCategory (Mod C.{u, v} A') := (originalModuleTransfer A').model
    (Mod.ExtensionOfScalars.adjunction p).IsQuillenEquivalence := by
  let : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
  let : ModelCategory (Mod C.{u, v} A') := (originalModuleTransfer A').model
  exact ModuleTransfer.WeakScalar.isQuillenEquivalenceOfRelativeFlatness
    (originalModuleTransfer A).weak_eq (originalModuleTransfer A').weak_eq
    (originalModuleTransfer A).fibrations_eq (originalModuleTransfer A').fibrations_eq p hp
    (fun M hM => originalModule_relativeFlat A M hM)

/-- The original same-rank Q and actual direct restriction give the native scalar derived equivalence. -/
def originalDirectDerivedEquivalence (p : A ⟶ A') [IsMonHom p]
    (hp : weakEquivalences C.{u, v} p) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
    letI : ModelCategory (Mod C.{u, v} A') := (originalModuleTransfer A').model
    (weakEquivalences (Mod C.{u, v} A)).Localization ≌
      (weakEquivalences (Mod C.{u, v} A')).Localization := by
  letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
  letI : ModelCategory (Mod C.{u, v} A') := (originalModuleTransfer A').model
  exact ModuleTransfer.WeakScalarDerived.directDerivedEquivalence
    (originalModuleTransfer A).weak_eq (originalModuleTransfer A').weak_eq
    (originalModuleTransfer A).fibrations_eq (originalModuleTransfer A').fibrations_eq p hp
    (fun M hM => originalModule_relativeFlat A M hM) (originalModuleTransfer A).replacements

/-- Both original same-cardinal generated Q/R factories retain the actual chosen derived scalar equivalence. -/
def originalReplacementDerivedEquivalence (p : A ⟶ A') [IsMonHom p]
    (hp : weakEquivalences C.{u, v} p) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
    letI : ModelCategory (Mod C.{u, v} A') := (originalModuleTransfer A').model
    (weakEquivalences (Mod C.{u, v} A)).Localization ≌
      (weakEquivalences (Mod C.{u, v} A')).Localization := by
  letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
  letI : ModelCategory (Mod C.{u, v} A') := (originalModuleTransfer A').model
  exact ModuleTransfer.WeakScalarDerived.replacementDerivedEquivalence
    (originalModuleTransfer A).weak_eq (originalModuleTransfer A').weak_eq
    (originalModuleTransfer A).fibrations_eq (originalModuleTransfer A').fibrations_eq p hp
    (fun M hM => originalModule_relativeFlat A M hM)
    (originalModuleTransfer A).replacements (originalModuleTransfer A').replacements

end HomotopicalAlgebra.ModuleTransfer.NativeOriginalRankSources.Symmetric

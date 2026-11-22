/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.OriginalFreeTensorClosedEmbedding
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ClosedSourceHom
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.SourceHomTransfer
import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer.OriginalRank
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.NativeScalarChange
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.WeakScalarDerived

/-!
# Original-rank orthogonal module source producers

Every original free-I boundary is pointwise closed after arbitrary native
coefficient tensor. The actual tensor functor and original cardinal cell
criterion extend that statement to the whole original cofibration class and
hence the full original K family. The whole forgotten module cell history is
closed; exact source Hom then constructs both original free-image algorithms,
the full module model, its replacements and weak scalar Quillen equivalences.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty CategoryTheory.SmallObject HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.NativeOriginalRankSources.Orthogonal

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

private abbrev C := Actual.OrthogonalCarrier.{u, v}
private abbrev I : MorphismProperty C.{u, v} :=
  NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
private abbrev J : MorphismProperty C.{u, v} := NativeK.generators Actual.orthogonalFamily.{u, v}
private abbrev Q : MorphismProperty C.{u, v} := ClosedSourceHom.pointwiseClosed

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash.monoidalCategory
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash.symmetricCategory
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed.monoidalClosed
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexMonoidalCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexEnrichedOrdinaryCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexSymmetricCategory

/-- The original orthogonal stable model at the retained realized-generator ordinal bottom. -/
local instance originalStableModel : ModelCategory C.{u, v} :=
  StableModelConstruction.orthogonalModelCategory (B := B)
local instance originalColimits : HasColimitsOfSize.{v, v} C.{u, v} :=
  { has_colimits_of_shape := fun _ _ => by infer_instance }
local instance originalIEligibility : I.{u, v}.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
    (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
local instance originalJEligibility : J.{u, v}.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  NativeK.generators_isCardinalForSmallObjectArgument Actual.orthogonalFamily.{u, v}
local instance originalLocallySmall : LocallySmall.{v} C.{u, v} :=
  SmallObject.locallySmall I realizedGeneratorCardinal.{v}

/-- The original cardinal cell criterion extends arbitrary coefficient closedness to every original I-left map. -/
theorem originalILeft_tensorClosed (N : C.{u, v}) {K L : C.{u, v}} (i : K ⟶ L)
    (hi : I.rlp.llp i) : Q (N ◁ i) := by
  intro b
  let P := TopCat.closedEmbeddings.inverseImage
    (PointedCGWH.pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v})
  let E : C.{u, v} ⥤ PointedCGWH.{u, v} :=
    tensorLeft N ⋙ EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) b
  let : PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType E :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  have hImage : I ≤ P.inverseImage E := by
    intro X Y f hf
    exact PointedCGWH.Spectra.Orthogonal.OriginalFreeTensorClosedEmbedding.originalI_leftTensor_component
      f hf N b
  exact rlp_llp_le_inverseImage_of_cardinal_closure I P E realizedGeneratorCardinal.{v} hImage i hi

variable (A : C.{u, v}) [MonObj A]

local instance moduleColimits : HasColimitsOfSize.{v, v} (Mod C.{u, v} A) := Mod.hasColimits.{v} A
local instance forgetColimits : PreservesColimitsOfSize.{v, v} (Mod.forget (D := C.{u, v}) A) :=
  ModuleTransfer.leftForgetPreservesColimits (Mon.mk A)
local instance forgetFaithful : (Mod.forget (D := C.{u, v}) A).Faithful :=
  { map_injective := fun h => Mod.hom_ext _ _ h }
local instance moduleLocallySmall : LocallySmall.{v} (Mod C.{u, v} A) :=
  locallySmall_of_faithful (Mod.forget (D := C.{u, v}) A)

/-- Every original free-I image retains its arbitrary scalar tensor in the whole pointwise closed class. -/
theorem originalFreeI_image : I.strictMap (Mod.free A) ≤ Q.inverseImage (Mod.forget (D := C.{u, v}) A) := by
  intro X Y f hf
  cases hf with
  | @map K L i hi =>
    change Q (A ◁ i)
    exact originalILeft_tensorClosed A i (I.le_llp_rlp i hi)

/-- Every full original K free image belongs to the same original closed class. -/
theorem originalFreeJ_image : J.strictMap (Mod.free A) ≤ Q.inverseImage (Mod.forget (D := C.{u, v}) A) := by
  intro X Y f hf
  cases hf with
  | @map K L i hi =>
    change Q (A ◁ i)
    have hC := J.le_llp_rlp i hi
    rw [(StableModelConstruction.orthogonal_five_classes (B := B)).2.2.1.symm, fibrations_llp] at hC
    have hI : I.rlp.llp i := by
      rw [(StableModelConstruction.orthogonal_five_classes (B := B)).2.2.2.2.symm, trivialFibrations_llp]
      exact hC.1
    exact originalILeft_tensorClosed A i hI

/-- The original free-I source Hom supplies all free-module source algorithm fields at the unchanged rank. -/
theorem originalFreeI_smallObject :
    (I.strictMap (Mod.free A)).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} := by
  let : I.IsSmall.{v} := SmallObject.isSmall I realizedGeneratorCardinal.{v}
  apply SourceHomTransfer.originalImageSmallObject (Mod.free A) (Mod.forget (D := C.{u, v}) A)
    (Mod.freeForgetAdjunction A) I Q realizedGeneratorCardinal.{v} (originalFreeI_image A)
  intro X Y i hi F _ hF
  exact ClosedSourceHom.originalISource_preservesClosedColimit i hi F (fun φ => hF φ)

/-- The full K source bank supplies the second free-module algorithm at the same original cardinal and bottom. -/
theorem originalFreeJ_smallObject :
    (J.strictMap (Mod.free A)).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} := by
  let : J.IsSmall.{v} := SmallObject.isSmall J realizedGeneratorCardinal.{v}
  apply SourceHomTransfer.originalImageSmallObject (Mod.free A) (Mod.forget (D := C.{u, v}) A)
    (Mod.freeForgetAdjunction A) J Q realizedGeneratorCardinal.{v} (originalFreeJ_image A)
  intro X Y i hi F _ hF
  exact ClosedSourceHom.originalJSource_preservesClosedColimit Actual.orthogonalFamily i hi F
    (fun φ => hF φ)

/-- Both actual original-rank source algorithms construct the complete orthogonal module model. -/
def originalModuleTransfer :
    RightTransfer.OriginalRankModelTransfer (Mod.free A) (Mod.forget (D := C.{u, v}) A)
      I J realizedGeneratorCardinal.{v} := by
  let : HasLimitsOfSize.{v, v} C.{u, v} := { has_limits_of_shape := fun _ _ => by infer_instance }
  let : HasLimitsOfSize.{v, v} (Mod C.{u, v} A) := Mod.hasLimits.{v} A
  let : (I.strictMap (Mod.free A)).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    originalFreeI_smallObject A
  let : (J.strictMap (Mod.free A)).IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    originalFreeJ_smallObject A
  let : MonoidAxiom.{v} C.{u, v} :=
    PointedCGWH.Spectra.Orthogonal.OriginalMonoidAxiomComplete.originalStableMonoidAxiom
  exact RightTransfer.originalRankModelTransfer (Mod.free A) (Mod.forget (D := C.{u, v}) A)
    I J realizedGeneratorCardinal.{v} (Mod.freeForgetAdjunction A)
    (StableModelConstruction.orthogonal_five_classes (B := B)).2.2.2.2.symm
    (StableModelConstruction.orthogonal_five_classes (B := B)).2.2.1.symm
    (ModuleTransfer.leftFreeJLeft_underlying_weak (Mon.mk A) J
      (StableModelConstruction.orthogonal_five_classes (B := B)).2.2.1.symm realizedGeneratorCardinal.{v})

/-- The created orthogonal module model retains exactly the original free-I cofibrations. -/
theorem originalModuleCofibrations :
    letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
    cofibrations (Mod C.{u, v} A) = (I.strictMap (Mod.free A)).rlp.llp := by
  let : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
  rw [← (originalModuleTransfer A).generation_I,
    (originalModuleTransfer A).generation.I_rlp, trivialFibrations_llp]

/-- Actual original-rank orthogonal module cofibrancy earns full relative flatness. -/
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
    (NativeSources.Orthogonal.originalStableCellClosure (B := B))
    (NativeSources.Orthogonal.originalI_coefficientFlatness (B := B))
    (fun N {K L} i hi => NativeSources.Orthogonal.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi)
    M f hf

variable {A} {A' : C.{u, v}} [MonObj A']

/-- The original balanced scalar unit is weak in the source-produced actual orthogonal module model. -/
theorem originalScalarUnit_weak (p : A ⟶ A') [IsMonHom p]
    (hp : weakEquivalences C.{u, v} p) (M : Mod C.{u, v} A) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
    IsCofibrant M → WeakEquivalence ((Mod.ExtensionOfScalars.adjunction p).unit.app M) := by
  let : ModelCategory (Mod C.{u, v} A) := (originalModuleTransfer A).model
  intro hM
  exact ModuleTransfer.WeakScalar.scalarUnit_weak (originalModuleTransfer A).weak_eq p hp M
    (originalModule_relativeFlat A M hM)

/-- The two fully source-produced original models give the actual scalar Quillen equivalence. -/
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

/-- The exact original module Q and direct restriction give the actual native scalar derived equivalence. -/
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

/-- Both same-original-rank Q/R factories retain the chosen derived scalar equivalence. -/
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

end HomotopicalAlgebra.ModuleTransfer.NativeOriginalRankSources.Orthogonal

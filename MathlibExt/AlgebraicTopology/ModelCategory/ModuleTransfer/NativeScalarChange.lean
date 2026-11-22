/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.NativeSources
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.WeakScalarOfTransfers

/-!
# Scalar change in the original native spectrum models

The original native monoid axiom and the caller's original free-I/free-K
source bounds construct the full module models. Native coefficient flatness
and the actual HEP cell comparisons then earn relative flatness and weak
scalar invariance. The source ranks and replacement factories are produced
by those transfers; no module model, flatness, scalar-unit or equivalence
outcome is an extra input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.SmallObject
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed CategoryTheory.MonObj

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

namespace HomotopicalAlgebra.ModuleTransfer.NativeScalarChange.Symmetric

private abbrev C := Actual.SymmetricCarrier.{u, v}
private abbrev I : MorphismProperty C.{u, v} :=
  NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev H : MorphismProperty C.{u, v} :=
  PointedCGWH.EnrichedBasedHomotopyExtension.property

variable [B₀ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

/-- The original symmetric stable model with the caller's chosen generator-cardinal bottom. -/
local instance originalStableModel : ModelCategory C.{u, v} :=
  StableModelConstruction.symmetricModelCategory (B := B₀)

private abbrev J : MorphismProperty C.{u, v} :=
  NativeK.generators Actual.symmetricFamily.{u, v}

/-- Original native generators, actual source bounds and the proved monoid axiom construct the full model. -/
def originalLeftModuleTransfer (A : C.{u, v}) [MonObj A]
    (sI : UniformRelativeSourceSmallness.{v} (I.strictMap (Mod.free A)))
    (sJ : UniformRelativeSourceSmallness.{v} (J.strictMap (Mod.free A))) :
    RightTransfer.FullModelTransfer (Mod.free A) (Mod.forget (D := C.{u, v}) A)
      I J sI sJ := by
  letI : I.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
  letI : J.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    NativeK.generators_isCardinalForSmallObjectArgument Actual.symmetricFamily.{u, v}
  letI : I.IsSmall.{v} := SmallObject.isSmall I realizedGeneratorCardinal.{v}
  letI : J.IsSmall.{v} :=
    SmallObject.isSmall J realizedGeneratorCardinal.{v}
  letI : LocallySmall.{v} C.{u, v} := SmallObject.locallySmall I realizedGeneratorCardinal.{v}
  letI : HasLimitsOfSize.{v, v} C.{u, v} :=
    { has_limits_of_shape := fun _ _ => by infer_instance }
  letI : MonoidAxiom.{v} C.{u, v} :=
    PointedCGWH.Spectra.Symmetric.OriginalMonoidAxiom.originalStableMonoidAxiom
  exact ModuleTransfer.fullLeftModuleModelTransfer (Mon.mk A) I J
    (StableModelConstruction.symmetric_five_classes (B := B₀)).2.2.2.2.symm
    (StableModelConstruction.symmetric_five_classes (B := B₀)).2.2.1.symm sI sJ

variable {A B : C.{u, v}} [MonObj A] [MonObj B]
  (sIA : UniformRelativeSourceSmallness.{v} (I.strictMap (Mod.free A)))
  (sJA : UniformRelativeSourceSmallness.{v} (J.strictMap (Mod.free A)))
  (sIB : UniformRelativeSourceSmallness.{v} (I.strictMap (Mod.free B)))
  (sJB : UniformRelativeSourceSmallness.{v} (J.strictMap (Mod.free B)))

/-- Every original cofibrant module is relatively flat in the model constructed from its source bounds. -/
theorem originalCofibrantModule_relativeFlat (M : Mod C.{u, v} A) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    IsCofibrant M → ModuleTransfer.WeakScalar.RelativeFlat M :=
  WeakScalarOfTransfers.relativeFlat_of_originalTransfer (originalLeftModuleTransfer A sIA sJA) H
    (NativeSources.Symmetric.originalStableCellClosure (B := B₀))
    (NativeSources.Symmetric.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Symmetric.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) M

/-- The actual scalar unit is weak on every cofibrant source module, with no scalar cofibrancy premise. -/
theorem originalScalarUnit_weak
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C.{u, v} p) (M : Mod C.{u, v} A) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    IsCofibrant M → WeakEquivalence ((Mod.ExtensionOfScalars.adjunction p).unit.app M) :=
  WeakScalarOfTransfers.scalarUnit_weak_of_originalTransfers (originalLeftModuleTransfer A sIA sJA) H
    (NativeSources.Symmetric.originalStableCellClosure (B := B₀))
    (NativeSources.Symmetric.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Symmetric.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) p hp M

/-- The two actual source-bound transfers give the original weak scalar Quillen equivalence. -/
theorem originalScalar_isQuillenEquivalence
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C.{u, v} p) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    letI : ModelCategory (Mod C.{u, v} B) := (originalLeftModuleTransfer B sIB sJB).model
    (Mod.ExtensionOfScalars.adjunction p).IsQuillenEquivalence :=
  WeakScalarOfTransfers.isQuillenEquivalence_of_originalTransfers
    (originalLeftModuleTransfer A sIA sJA) (originalLeftModuleTransfer B sIB sJB) H
    (NativeSources.Symmetric.originalStableCellClosure (B := B₀))
    (NativeSources.Symmetric.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Symmetric.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) p hp

/-- The returned source rank and the actual direct localized restriction give the derived equivalence. -/
def originalDirectDerivedEquivalence
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C.{u, v} p) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    letI : ModelCategory (Mod C.{u, v} B) := (originalLeftModuleTransfer B sIB sJB).model
    (weakEquivalences (Mod C.{u, v} A)).Localization ≌
      (weakEquivalences (Mod C.{u, v} B)).Localization :=
  WeakScalarOfTransfers.directDerivedEquivalence
    (originalLeftModuleTransfer A sIA sJA) (originalLeftModuleTransfer B sIB sJB) H
    (NativeSources.Symmetric.originalStableCellClosure (B := B₀))
    (NativeSources.Symmetric.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Symmetric.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) p hp

/-- Both independently produced source ranks retain the original M4 chosen-Q/chosen-R equivalence. -/
def originalReplacementDerivedEquivalence
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C.{u, v} p) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    letI : ModelCategory (Mod C.{u, v} B) := (originalLeftModuleTransfer B sIB sJB).model
    (weakEquivalences (Mod C.{u, v} A)).Localization ≌
      (weakEquivalences (Mod C.{u, v} B)).Localization :=
  WeakScalarOfTransfers.replacementDerivedEquivalence
    (originalLeftModuleTransfer A sIA sJA) (originalLeftModuleTransfer B sIB sJB) H
    (NativeSources.Symmetric.originalStableCellClosure (B := B₀))
    (NativeSources.Symmetric.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Symmetric.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) p hp

end HomotopicalAlgebra.ModuleTransfer.NativeScalarChange.Symmetric

namespace HomotopicalAlgebra.ModuleTransfer.NativeScalarChange.Orthogonal

private abbrev C := Actual.OrthogonalCarrier.{u, v}
private abbrev I : MorphismProperty C.{u, v} :=
  NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
private abbrev H : MorphismProperty C.{u, v} :=
  PointedCGWH.EnrichedBasedHomotopyExtension.property

variable [B₀ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

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

/-- The original orthogonal stable model with the caller's chosen generator-cardinal bottom. -/
local instance originalStableModel : ModelCategory C.{u, v} :=
  StableModelConstruction.orthogonalModelCategory (B := B₀)

private abbrev J : MorphismProperty C.{u, v} :=
  NativeK.generators Actual.orthogonalFamily.{u, v}

/-- Original native generators, actual source bounds and the proved monoid axiom construct the full model. -/
def originalLeftModuleTransfer (A : C.{u, v}) [MonObj A]
    (sI : UniformRelativeSourceSmallness.{v} (I.strictMap (Mod.free A)))
    (sJ : UniformRelativeSourceSmallness.{v} (J.strictMap (Mod.free A))) :
    RightTransfer.FullModelTransfer (Mod.free A) (Mod.forget (D := C.{u, v}) A)
      I J sI sJ := by
  letI : I.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
  letI : J.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
    NativeK.generators_isCardinalForSmallObjectArgument Actual.orthogonalFamily.{u, v}
  letI : I.IsSmall.{v} := SmallObject.isSmall I realizedGeneratorCardinal.{v}
  letI : J.IsSmall.{v} :=
    SmallObject.isSmall J realizedGeneratorCardinal.{v}
  letI : LocallySmall.{v} C.{u, v} := SmallObject.locallySmall I realizedGeneratorCardinal.{v}
  letI : HasLimitsOfSize.{v, v} C.{u, v} :=
    { has_limits_of_shape := fun _ _ => by infer_instance }
  letI : MonoidAxiom.{v} C.{u, v} :=
    PointedCGWH.Spectra.Orthogonal.OriginalMonoidAxiomComplete.originalStableMonoidAxiom
  exact ModuleTransfer.fullLeftModuleModelTransfer (Mon.mk A) I J
    (StableModelConstruction.orthogonal_five_classes (B := B₀)).2.2.2.2.symm
    (StableModelConstruction.orthogonal_five_classes (B := B₀)).2.2.1.symm sI sJ

variable {A B : C.{u, v}} [MonObj A] [MonObj B]
  (sIA : UniformRelativeSourceSmallness.{v} (I.strictMap (Mod.free A)))
  (sJA : UniformRelativeSourceSmallness.{v} (J.strictMap (Mod.free A)))
  (sIB : UniformRelativeSourceSmallness.{v} (I.strictMap (Mod.free B)))
  (sJB : UniformRelativeSourceSmallness.{v} (J.strictMap (Mod.free B)))

/-- Every original cofibrant module is relatively flat in the model constructed from its source bounds. -/
theorem originalCofibrantModule_relativeFlat (M : Mod C.{u, v} A) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    IsCofibrant M → ModuleTransfer.WeakScalar.RelativeFlat M :=
  WeakScalarOfTransfers.relativeFlat_of_originalTransfer (originalLeftModuleTransfer A sIA sJA) H
    (NativeSources.Orthogonal.originalStableCellClosure (B := B₀))
    (NativeSources.Orthogonal.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Orthogonal.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) M

/-- The actual scalar unit is weak on every cofibrant source module, with no scalar cofibrancy premise. -/
theorem originalScalarUnit_weak
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C.{u, v} p) (M : Mod C.{u, v} A) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    IsCofibrant M → WeakEquivalence ((Mod.ExtensionOfScalars.adjunction p).unit.app M) :=
  WeakScalarOfTransfers.scalarUnit_weak_of_originalTransfers (originalLeftModuleTransfer A sIA sJA) H
    (NativeSources.Orthogonal.originalStableCellClosure (B := B₀))
    (NativeSources.Orthogonal.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Orthogonal.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) p hp M

/-- The two actual source-bound transfers give the original weak scalar Quillen equivalence. -/
theorem originalScalar_isQuillenEquivalence
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C.{u, v} p) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    letI : ModelCategory (Mod C.{u, v} B) := (originalLeftModuleTransfer B sIB sJB).model
    (Mod.ExtensionOfScalars.adjunction p).IsQuillenEquivalence :=
  WeakScalarOfTransfers.isQuillenEquivalence_of_originalTransfers
    (originalLeftModuleTransfer A sIA sJA) (originalLeftModuleTransfer B sIB sJB) H
    (NativeSources.Orthogonal.originalStableCellClosure (B := B₀))
    (NativeSources.Orthogonal.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Orthogonal.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) p hp

/-- The returned source rank and the actual direct localized restriction give the derived equivalence. -/
def originalDirectDerivedEquivalence
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C.{u, v} p) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    letI : ModelCategory (Mod C.{u, v} B) := (originalLeftModuleTransfer B sIB sJB).model
    (weakEquivalences (Mod C.{u, v} A)).Localization ≌
      (weakEquivalences (Mod C.{u, v} B)).Localization :=
  WeakScalarOfTransfers.directDerivedEquivalence
    (originalLeftModuleTransfer A sIA sJA) (originalLeftModuleTransfer B sIB sJB) H
    (NativeSources.Orthogonal.originalStableCellClosure (B := B₀))
    (NativeSources.Orthogonal.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Orthogonal.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) p hp

/-- Both independently produced source ranks retain the original M4 chosen-Q/chosen-R equivalence. -/
def originalReplacementDerivedEquivalence
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C.{u, v} p) :
    letI : ModelCategory (Mod C.{u, v} A) := (originalLeftModuleTransfer A sIA sJA).model
    letI : ModelCategory (Mod C.{u, v} B) := (originalLeftModuleTransfer B sIB sJB).model
    (weakEquivalences (Mod C.{u, v} A)).Localization ≌
      (weakEquivalences (Mod C.{u, v} B)).Localization :=
  WeakScalarOfTransfers.replacementDerivedEquivalence
    (originalLeftModuleTransfer A sIA sJA) (originalLeftModuleTransfer B sIB sJB) H
    (NativeSources.Orthogonal.originalStableCellClosure (B := B₀))
    (NativeSources.Orthogonal.originalI_coefficientFlatness (B := B₀))
    (fun N {K L} i hi => NativeSources.Orthogonal.originalI_leftTensor_HEP N.X (K := K) (L := L) i hi) p hp

end HomotopicalAlgebra.ModuleTransfer.NativeScalarChange.Orthogonal

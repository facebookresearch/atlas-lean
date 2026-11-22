/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePiHoDetection
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Original integer groups detect the actual integer localization

The original RT and native Q/K units on original Omega objects give
isomorphisms of the whole ordinary-Ho arrows. The actual integer
localization adjunction and its fully faithful right functor then detect
the full original integer class. The original integer group functors are
jointly conservative on both the original Omega category and the actual
integer localization, retaining every original source map and unit.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeIntegerLocalizationGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableLocalizationGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.LevelIntegerStableLocalizationGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableAdjunctionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoDetectionGeometry
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope
namespace IntegerStablePiLocalizationDetectionGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev Ho := HomotopyCategory Carrier.{u, v}
private abbrev family : NativeStabilizationFamily.{u, v}
    (CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v}) ℕ :=
  PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

/-- The original Omega-unit isomorphisms retain the entire original RT Arrow square. -/
def originalOmegaReflectionArrowIso {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    Arrow.mk f.hom ≅ Arrow.mk (reflectionHoFunctor.map f.hom) :=
  Arrow.isoMk (reflectionOmegaHoUnitIso X) (reflectionOmegaHoUnitIso Y)
    (reflectionHoUnit.naturality f.hom).symm

/-- The complete forward source function is the original RT unit at that same Omega object. -/
theorem originalOmegaReflectionArrowIso_hom_left
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    (originalOmegaReflectionArrowIso f).hom.left = reflectionHoUnit.app X.obj := rfl

/-- The complete forward target function is the original RT unit at that same Omega object. -/
theorem originalOmegaReflectionArrowIso_hom_right
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    (originalOmegaReflectionArrowIso f).hom.right = reflectionHoUnit.app Y.obj := rfl

/-- The complete inverse source function is the actual original Omega-unit inverse. -/
theorem originalOmegaReflectionArrowIso_inv_left
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    (originalOmegaReflectionArrowIso f).inv.left = (reflectionOmegaHoUnitIso X).inv := rfl

/-- The complete inverse target function is the actual original Omega-unit inverse. -/
theorem originalOmegaReflectionArrowIso_inv_right
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    (originalOmegaReflectionArrowIso f).inv.right = (reflectionOmegaHoUnitIso Y).inv := rfl

/-- The original native Q-inverse/K-unit retains the entire Arrow square on Omega objects. -/
def originalOmegaNativeQKArrowIso {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    Arrow.mk f.hom ≅ Arrow.mk ((NativeK.localReplacementHo family).map f.hom) :=
  Arrow.isoMk (nativeQKOriginalOmegaUnitIso X) (nativeQKOriginalOmegaUnitIso Y)
    ((NativeK.localReplacementHoUnit family).naturality f.hom).symm

/-- The full native forward source function is the same original Q-inverse/K-unit. -/
theorem originalOmegaNativeQKArrowIso_hom_left
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    (originalOmegaNativeQKArrowIso f).hom.left =
      (NativeK.localReplacementHoUnit family).app X.obj := rfl

/-- The full native forward target function is the same original Q-inverse/K-unit. -/
theorem originalOmegaNativeQKArrowIso_hom_right
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    (originalOmegaNativeQKArrowIso f).hom.right =
      (NativeK.localReplacementHoUnit family).app Y.obj := rfl

/-- The full native inverse source function is the original native Omega-unit inverse. -/
theorem originalOmegaNativeQKArrowIso_inv_left
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    (originalOmegaNativeQKArrowIso f).inv.left = (nativeQKOriginalOmegaUnitIso X).inv := rfl

/-- The full native inverse target function is the original native Omega-unit inverse. -/
theorem originalOmegaNativeQKArrowIso_inv_right
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    (originalOmegaNativeQKArrowIso f).inv.right = (nativeQKOriginalOmegaUnitIso Y).inv := rfl

/-- Original integer Ho groups detect every whole arrow in the original Omega full subcategory. -/
theorem originalOmega_integerPiHo_iff_isIso
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    integerPiHoEquivalences f.hom ↔ IsIso f := by
  have h : IsIso f.hom ↔ IsIso (reflectionHoFunctor.map f.hom) :=
    (MorphismProperty.isomorphisms Ho.{u, v}).arrow_mk_iso_iff
      (originalOmegaReflectionArrowIso f)
  exact (integerPiHoEquivalences_iff_reflection_isIso f.hom).trans
    (h.symm.trans (isIso_iff_of_reflects_iso f omegaHoObjects.ι))

/-- Both whole original native image functions detect every original Omega arrow. -/
theorem originalOmega_nativeQKMap_isIso_iff
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    IsIso ((NativeK.localReplacementHo family).map f.hom) ↔ IsIso f := by
  have h : IsIso f.hom ↔ IsIso ((NativeK.localReplacementHo family).map f.hom) :=
    (MorphismProperty.isomorphisms Ho.{u, v}).arrow_mk_iso_iff
      (originalOmegaNativeQKArrowIso f)
  exact h.symm.trans (isIso_iff_of_reflects_iso f omegaHoObjects.ι)

/-- Every original degree group and every whole original Omega map participates in detection. -/
theorem integerStablePiOmegaFunctor_jointly_reflects_isomorphisms
    {X Y : omegaHoObjects.{u, v}.FullSubcategory} (f : X ⟶ Y) :
    (∀ q : ℤ, IsIso ((integerStablePiOmegaFunctor q).map f)) ↔ IsIso f :=
  (integerPiHoEquivalences_iff f.hom).symm.trans (originalOmega_integerPiHo_iff_isIso f)

/-- The actual right functor and whole original functor identity detect the integer projection. -/
theorem integerPiHoEquivalences_iff_integerProjection_isIso
    {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences f ↔ IsIso (levelToIntegerStableHo.map f) := by
  let R : IntegerStableHomotopyCategory.{u, v} ⥤ Ho.{u, v} := integerStableToLevelHo
  let _ : R.Full := integerStableToLevelHo_full
  let _ : R.Faithful := integerStableToLevelHo_faithful
  have h : IsIso (R.map (levelToIntegerStableHo.map f)) ↔
      IsIso (reflectionHoFunctor.map f) :=
    NatIso.isIso_map_iff (eqToIso integerStableAdjunction_originalFunctor) f
  exact (integerPiHoEquivalences_iff_reflection_isIso f).trans
    (h.symm.trans (isIso_iff_of_reflects_iso (levelToIntegerStableHo.map f) R))

/-- The original all-degree Ho class is exactly the inverse image of the actual integer Isos. -/
theorem integerPiHoEquivalences_eq_integerProjectionInverseImage :
    integerPiHoEquivalences.{u, v} =
      (MorphismProperty.isomorphisms IntegerStableHomotopyCategory).inverseImage
        levelToIntegerStableHo := by
  funext X Y f
  exact propext (integerPiHoEquivalences_iff_integerProjection_isIso f)

/-- Both actual original native and integer-projection images detect the same whole Ho arrow. -/
theorem nativeQKHoMap_isIso_iff_integerProjection
    {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    IsIso ((NativeK.localReplacementHo family).map f) ↔ IsIso (levelToIntegerStableHo.map f) :=
  (integerPiHoEquivalences_iff_nativeQK_isIso f).symm.trans
    (integerPiHoEquivalences_iff_integerProjection_isIso f)

/-- The actual original integer source projection reflects every original integer testing arrow. -/
theorem integerPiStarEquivalences_iff_integerStableProjection_isIso
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences f ↔ IsIso (integerStableProjection.map f) := by
  have h : integerPiStarEquivalences f ↔
      IsIso (levelToIntegerStableHo.map (H.map f)) :=
    (integerPiHoEquivalences_projected f).symm.trans
      (integerPiHoEquivalences_iff_integerProjection_isIso (H.map f))
  exact h.trans (Iff.of_eq (congrArg
    (fun g : integerStableProjection.obj X ⟶ integerStableProjection.obj Y => IsIso g)
    (levelToIntegerStableHo_map f)))

/-- The original integer source class is precisely the actual projection's isomorphism class. -/
theorem integerPiStarEquivalences_eq_integerStableProjectionInverseImage :
    integerPiStarEquivalences.{u, v} =
      (MorphismProperty.isomorphisms IntegerStableHomotopyCategory).inverseImage
        integerStableProjection := by
  funext X Y f
  exact propext (integerPiStarEquivalences_iff_integerStableProjection_isIso f)

/-- The same entire original native K-local-test source class is detected by that projection. -/
theorem nativeLocalTests_iff_integerStableProjection_isIso
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    NativeK.localTestEquivalences family f ↔ IsIso (integerStableProjection.map f) :=
  (nativeLocalTests_iff_originalIntegerPiStar f).trans
    (integerPiStarEquivalences_iff_integerStableProjection_isIso f)

/-- All original integer groups detect every arbitrary arrow of the actual integer localization. -/
theorem integerStablePiStableFunctor_jointly_reflects_isomorphisms
    {X Y : IntegerStableHomotopyCategory.{u, v}} (f : X ⟶ Y) :
    (∀ q : ℤ, IsIso ((integerStablePiStableFunctor q).map f)) ↔ IsIso f :=
  (forall_congr' (fun q => NatIso.isIso_map_iff (integerStableOmegaPiNatIso q) f)).trans
    ((integerStablePiOmegaFunctor_jointly_reflects_isomorphisms
      (integerStableOmegaEquivalence.functor.map f)).trans
        (isIso_iff_of_reflects_iso f integerStableOmegaEquivalence.functor))

/-- Every actual integer-localization isomorphism is detected by the original right Ho functor. -/
theorem integerStableToLevelHo_map_isIso_iff
    {X Y : IntegerStableHomotopyCategory.{u, v}} (f : X ⟶ Y) :
    IsIso (integerStableToLevelHo.map f) ↔ IsIso f := by
  let _ := integerStableToLevelHo_full
  let _ := integerStableToLevelHo_faithful
  exact isIso_iff_of_reflects_iso f integerStableToLevelHo

/-- The complete original right-Ho image retains all the same original degree tests. -/
theorem integerStableToLevelHo_integerPiHo_iff_isIso
    {X Y : IntegerStableHomotopyCategory.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences (integerStableToLevelHo.map f) ↔ IsIso f :=
  (originalOmega_integerPiHo_iff_isIso (integerStableOmegaEquivalence.functor.map f)).trans
    (isIso_iff_of_reflects_iso f integerStableOmegaEquivalence.functor)

/-- The full original native Q/K map of the right image detects every integer-localization arrow. -/
theorem integerStableToLevelHo_nativeQKMap_isIso_iff
    {X Y : IntegerStableHomotopyCategory.{u, v}} (f : X ⟶ Y) :
    IsIso ((NativeK.localReplacementHo family).map (integerStableToLevelHo.map f)) ↔ IsIso f :=
  (integerPiHoEquivalences_iff_nativeQK_isIso (integerStableToLevelHo.map f)).symm.trans
    (integerStableToLevelHo_integerPiHo_iff_isIso f)

/-- The same actual original RT unit becomes an Iso under the original integer projection. -/
theorem reflectionHoUnit_integerProjection_isIso (X : Ho.{u, v}) :
    IsIso (levelToIntegerStableHo.map (reflectionHoUnit.app X)) :=
  (integerPiHoEquivalences_iff_integerProjection_isIso (reflectionHoUnit.app X)).mp
    (reflectionHoUnit_integerPiHo X)

/-- The same original Q-inverse/K-unit becomes an Iso under that same original projection. -/
theorem nativeQKHoUnit_integerProjection_isIso (X : Ho.{u, v}) :
    IsIso (levelToIntegerStableHo.map ((NativeK.localReplacementHoUnit family).app X)) :=
  (integerPiHoEquivalences_iff_integerProjection_isIso
    ((NativeK.localReplacementHoUnit family).app X)).mp (nativeQKHoUnit_integerPiHo X)

end IntegerStablePiLocalizationDetectionGeometry
end PointedCGWH.SequentialSpectrum.MappingTelescope

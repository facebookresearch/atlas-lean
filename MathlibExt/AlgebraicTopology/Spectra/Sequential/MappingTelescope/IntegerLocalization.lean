/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.RTReflection
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
import Mathlib.CategoryTheory.Localization.Composition

/-!
# Actual original integer and native local-test categorical localization

The complete original T-then-R reflector localizes all original integer
degree tests. The ordinary-Ho image class and unit membership come from
the actual original integer unit maps. The native Q/K comparison then
identifies this with the entire original native local-test class, keeping
the same source functor, maps, ordinary-Ho Hom functions and inverse.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerOmegaRecognitionGeometry
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.NativeIntegerLocalizationGeometry

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

/-- The whole ordinary-Ho class is the actual image of every original integer testing arrow. -/
def originalIntegerHoClass : MorphismProperty Ho.{u, v} :=
  integerPiStarEquivalences.map H

private instance originalIntegerHoClass_respectsIso :
    originalIntegerHoClass.{u, v}.RespectsIso := by
  unfold originalIntegerHoClass
  infer_instance

/-- Every original integer arrow is inverted by the same full original T-then-R reflector. -/
theorem reflectionOmegaHoFunctor_inverts_originalInteger :
    integerPiStarEquivalences.{u, v}.IsInvertedBy (H ⋙ reflectionOmegaHoFunctor) := by
  intro X Y f hf
  have h : IsIso (reflectionHoFunctor.map (H.map f)) := by
    rw [reflectionHoFunctor_map]
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
      ((integerPiStar_iff_reflectionLevelWeak f).mp hf)
  change IsIso (reflectionOmegaHoFunctor.map (H.map f))
  let _ : IsIso (omegaHoObjects.ι.map (reflectionOmegaHoFunctor.map (H.map f))) := h
  exact isIso_of_reflects_iso _ omegaHoObjects.ι

/-- The entire ordinary-Ho image class is inverted by the same original Omega reflector. -/
theorem reflectionOmegaHoFunctor_inverts_originalIntegerHo :
    originalIntegerHoClass.{u, v}.IsInvertedBy reflectionOmegaHoFunctor := by
  simpa only [originalIntegerHoClass, MorphismProperty.IsInvertedBy.map_iff] using
    reflectionOmegaHoFunctor_inverts_originalInteger

/-- Every actual original ordinary-Ho unit belongs to the full original integer image class. -/
theorem reflectionOmegaHoAdjunction_unit_originalIntegerHo (X : Ho.{u, v}) :
    originalIntegerHoClass (reflectionOmegaHoAdjunction.unit.app X) := by
  obtain ⟨X, rfl⟩ := (Localization.Construction.objEquiv
    (weakEquivalences Carrier.{u, v})).surjective X
  change originalIntegerHoClass (reflectionOmegaHoAdjunction.unit.app (H.obj X))
  rw [reflectionOmegaHoAdjunction_unit_app, reflectionHoUnit_app]
  exact integerPiStarEquivalences.map_mem_map H (reflectionUnit.app X)
    (reflectionUnit_integerPiStar X)

/-- The original full Omega adjunction localizes all ordinary-Ho integer tests. -/
theorem reflectionOmegaHoFunctor_isOriginalIntegerHoLocalization :
    reflectionOmegaHoFunctor.{u, v}.IsLocalization originalIntegerHoClass :=
  reflectionOmegaHoAdjunction.isLocalization_leftAdjoint originalIntegerHoClass
    reflectionOmegaHoFunctor_inverts_originalIntegerHo
    reflectionOmegaHoAdjunction_unit_originalIntegerHo

/-- The entire source localization keeps the original level projection and T-then-R reflector. -/
def originalIntegerLocalization : Carrier.{u, v} ⥤ omegaHoObjects.FullSubcategory :=
  H ⋙ reflectionOmegaHoFunctor

/-- The source functor is an actual categorical localization at all original integer degrees. -/
theorem originalIntegerLocalization_isLocalization :
    originalIntegerLocalization.{u, v}.IsLocalization integerPiStarEquivalences := by
  let _ : reflectionOmegaHoFunctor.{u, v}.IsLocalization originalIntegerHoClass :=
    reflectionOmegaHoFunctor_isOriginalIntegerHoLocalization
  exact Functor.IsLocalization.comp
    (L₁ := H) (W₁ := weakEquivalences Carrier.{u, v})
    (L₂ := reflectionOmegaHoFunctor) (W₂ := originalIntegerHoClass)
    integerPiStarEquivalences reflectionOmegaHoFunctor_inverts_originalInteger
    (fun _ _ f hf => levelWeak_le_integerPiStarEquivalences f hf) le_rfl

/-- The same source functor localizes the entire original canonical native K-local test class. -/
theorem originalIntegerLocalization_isNativeLocalTestLocalization :
    originalIntegerLocalization.{u, v}.IsLocalization (NativeK.localTestEquivalences family) := by
  have h : NativeK.localTestEquivalences family = integerPiStarEquivalences.{u, v} :=
    nativeLocalTestEquivalences_eq_originalIntegerPiStar
  rw [h]
  exact originalIntegerLocalization_isLocalization

/-- Every original source object retains precisely the actual original R(T(X)) Ho object. -/
theorem originalIntegerLocalization_obj (X : Carrier.{u, v}) :
    (originalIntegerLocalization.obj X).obj = H.obj (reflectionFunctor.obj X) :=
  reflectionHoFunctor_obj X

/-- Every original source arrow retains the entire original T-map followed by the R-map. -/
theorem originalIntegerLocalization_map {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (originalIntegerLocalization.map f).hom = H.map (reflectionFunctor.map f) :=
  reflectionHoFunctor_map f

/-- The entire localization's forward Hom function keeps the same original two-map unit. -/
def originalIntegerLocalizationHomEquiv (X : Carrier.{u, v})
    (Z : omegaHoObjects.FullSubcategory) :
    (originalIntegerLocalization.obj X ⟶ Z) ≃ (H.obj X ⟶ Z.obj) :=
  reflectionOmegaHoHomEquiv (H.obj X) Z

/-- Every full source Hom input is precomposed with both original unit maps. -/
theorem originalIntegerLocalizationHomEquiv_apply (X : Carrier.{u, v})
    (Z : omegaHoObjects.FullSubcategory) (g : originalIntegerLocalization.obj X ⟶ Z) :
    originalIntegerLocalizationHomEquiv X Z g = H.map (reflectionUnit.app X) ≫ g.hom := by
  exact (reflectionOmegaHoHomEquiv_apply (H.obj X) Z g).trans
    (congrArg (fun a => a ≫ g.hom) (reflectionHoUnit_app X))

/-- Every full inverse input uses the original descended R/T functor and original unit inverse. -/
theorem originalIntegerLocalizationHomEquiv_symm_apply (X : Carrier.{u, v})
    (Z : omegaHoObjects.FullSubcategory) (f : H.obj X ⟶ Z.obj) :
    ((originalIntegerLocalizationHomEquiv X Z).symm f).hom =
      reflectionHoFunctor.map f ≫ (reflectionOmegaHoUnitIso Z).inv :=
  reflectionOmegaHoHomEquiv_symm_apply (H.obj X) Z f

/-- Arbitrary original source maps retain the whole forward Hom naturality of this localization. -/
theorem originalIntegerLocalizationHomEquiv_source
    {X X' : Carrier.{u, v}} (a : X' ⟶ X) (Z : omegaHoObjects.FullSubcategory)
    (g : originalIntegerLocalization.obj X ⟶ Z) :
    originalIntegerLocalizationHomEquiv X' Z (originalIntegerLocalization.map a ≫ g) =
      H.map a ≫ originalIntegerLocalizationHomEquiv X Z g :=
  reflectionOmegaHoHomEquiv_source (H.map a) Z g

/-- Arbitrary original source maps retain the whole inverse Hom naturality of this localization. -/
theorem originalIntegerLocalizationHomEquiv_source_symm
    {X X' : Carrier.{u, v}} (a : X' ⟶ X) (Z : omegaHoObjects.FullSubcategory)
    (f : H.obj X ⟶ Z.obj) :
    (originalIntegerLocalizationHomEquiv X' Z).symm (H.map a ≫ f) =
      originalIntegerLocalization.map a ≫ (originalIntegerLocalizationHomEquiv X Z).symm f :=
  reflectionOmegaHoHomEquiv_source_symm (H.map a) Z f

end PointedCGWH.SequentialSpectrum.MappingTelescope.NativeIntegerLocalizationGeometry

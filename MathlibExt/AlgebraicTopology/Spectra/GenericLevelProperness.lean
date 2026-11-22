/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveMappedProperness
import MathlibExt.AlgebraicTopology.Spectra.Sequential.GenericOriginalLevelModel
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.GenericOriginalLevelModel

/-!
# Left properness of the actual generic T-spectrum level models

The original generation, cardinal, ordinal bottom and evaluated source-Hom
conditions construct the same four level models. Cofibrancy of T proves
generator tensor membership; degree zero uses the original unitors.
The actual model classes and factor choices are retained throughout.
-/

set_option autoImplicit false

noncomputable section

universe w uV vV

open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory
open scoped MonoidalClosed

namespace HomotopicalAlgebra

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [ModelCategory V] [IsClosedSymmetricMonoidalModelCategory V]
  [hBaseProper : IsLeftProper V] [HasColimitsOfSize.{w, w} V] [LocallySmall.{w} V]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

local instance smallColimits : HasColimitsOfSize.{0, 0} V :=
  hasColimitsOfSizeShrink.{0, 0, w, w} V

include hBaseProper

namespace GenericSequentialLevel

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable (T : V) [IsCofibrant T] (d : CofibrantGenerationData V κ)
  (hSourceI : SourceCondition (κ := κ) T d.I) (hSourceJ : SourceCondition (κ := κ) T d.J)

/-- The actual canonical sequential level model is left proper at the same original source data. -/
theorem canonicalModelCategory_isLeftProper :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    IsLeftProper (CategoryTheory.Spectra.Sequential.Spectrum T) := by
  let _ : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
    canonicalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.modelCategory_isLeftProper d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf))

/-- The same actual sequential model is left proper on the original spectrum carrier. -/
theorem originalModelCategory_isLeftProper :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    IsLeftProper (SequentialSpectrum V T) := by
  let _ : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.sourceModelCategory_isLeftProper d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf))
    (SequentialSpectrum.EnrichedPresentation.enrichedEquivalence T)

end GenericSequentialLevel

namespace GenericSymmetricLevel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable (T : V) [IsCofibrant T] (d : CofibrantGenerationData V κ)
  (hSourceI : SourceCondition (κ := κ) T d.I) (hSourceJ : SourceCondition (κ := κ) T d.J)

/-- Every finite-index canonical symmetric level model is left proper with its original source data. -/
theorem canonicalModelCategory_isLeftProper :
    letI : ModelCategory (GenericSphereOperatorSpectra T) := canonicalModelCategory T d hSourceI hSourceJ
    IsLeftProper (GenericSphereOperatorSpectra T) := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (GenericSphereOperatorSpectra T) := canonicalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.modelCategory_isLeftProper d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf))

/-- The actual ordinary S(T)-module level model is left proper on its unchanged original carrier. -/
theorem originalModelCategory_isLeftProper :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    IsLeftProper (SymmetricSpectrum (genericSphereDayMonoid T)) := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
    originalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.sourceModelCategory_isLeftProper d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf))
    (genericSphereModuleOperatorEquivalence T)

end GenericSymmetricLevel

end HomotopicalAlgebra

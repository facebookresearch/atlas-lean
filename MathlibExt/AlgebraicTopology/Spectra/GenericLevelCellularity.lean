/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveMappedCellularity
import MathlibExt.AlgebraicTopology.Spectra.GenericLevelProperness

/-!
# Cellular sources of the actual generic T-spectrum level models

The original coefficient generation, common cardinal and source conditions
construct the same sequential and symmetric models. Their actual free and
evaluation functors transpose source Hom along the original cell chains.
Their original cofibrations equalize their original self-pushout inclusions.
-/

set_option autoImplicit false

noncomputable section

universe w uV vV

open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory
open scoped MonoidalClosed

namespace HomotopicalAlgebra

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [ModelCategory V] [IsClosedSymmetricMonoidalModelCategory V]
  [HasColimitsOfSize.{w, w} V] [LocallySmall.{w} V]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

local instance cellularitySmallColimits : HasColimitsOfSize.{0, 0} V :=
  hasColimitsOfSizeShrink.{0, 0, w, w} V

namespace GenericSequentialLevel

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

omit [IsClosedSymmetricMonoidalModelCategory V] [LocallySmall.{w} V] in
/-- Every actual raw degree evaluation preserves working-size colimits by its original presentation. -/
theorem originalEvaluation_preservesColimitsOfSize (T : V) (n : ℕ) :
    PreservesColimitsOfSize.{w, w} (SequentialSpectrum.evaluation T n) :=
  preservesColimits_of_natIso
    (originalEvaluationIso T (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree T n))

variable (T : V) [IsCofibrant T] (d : CofibrantGenerationData V κ)
  (hSourceI : SourceCondition (κ := κ) T d.I)
  (hSourceJ : SourceCondition (κ := κ) T d.J)

include hSourceI hSourceJ

/-- The canonical sequential free families retain the original generation cardinal and bottom. -/
def canonicalGenerationData :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    CofibrantGenerationData (CategoryTheory.Spectra.Sequential.Spectrum T) κ :=
  EnrichedProjective.MappedSources.generationData d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ

/-- The actual canonical sequential free I family is unchanged. -/
theorem canonicalGenerationData_I :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    (canonicalGenerationData T d hSourceI hSourceJ).I = generators T d.I := rfl

/-- The actual canonical sequential free J family is unchanged. -/
theorem canonicalGenerationData_J :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    (canonicalGenerationData T d hSourceI hSourceJ).J = generators T d.J := rfl

/-- The exact raw free I/J families have generation data at the unchanged original cardinal. -/
def originalGenerationData :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    CofibrantGenerationData (SequentialSpectrum V T) κ :=
  EnrichedProjective.MappedSources.sourceGenerationData d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (SequentialSpectrum.EnrichedPresentation.enrichedEquivalence T)
    (fun a => SequentialSpectrum.evaluation T a.degree) (originalEvaluationIso T)
    (fun a => SequentialSpectrum.freeAt T a.degree)
    (fun a => SequentialSpectrum.freeAtEvaluationAdjunction T a.degree)

/-- The unchanged original sequential free I arrows are the recorded generating family. -/
theorem originalGenerationData_I :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    (originalGenerationData T d hSourceI hSourceJ).I = originalGenerators T d.I := rfl

/-- The unchanged original sequential free J arrows are the recorded generating family. -/
theorem originalGenerationData_J :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    (originalGenerationData T d hSourceI hSourceJ).J = originalGenerators T d.J := rfl

/-- Every original canonical sequential cofibration is a genuine regular monomorphism. -/
theorem canonicalModelCategory_cofibrations_regularMono (eff : EffectiveCofibrations V) :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    cofibrations (CategoryTheory.Spectra.Sequential.Spectrum T) ≤
      regularMono (CategoryTheory.Spectra.Sequential.Spectrum T) := by
  let _ : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
    canonicalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.modelCategory_cofibrations_regularMono d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf)) eff

/-- Every original raw sequential cofibration is a genuine regular monomorphism. -/
theorem originalModelCategory_cofibrations_regularMono (eff : EffectiveCofibrations V) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    cofibrations (SequentialSpectrum V T) ≤ regularMono (SequentialSpectrum V T) := by
  let _ : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.sourceModelCategory_cofibrations_regularMono d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf)) eff
    (SequentialSpectrum.EnrichedPresentation.enrichedEquivalence T)

/-- A raw sequential cofibration equalizes its two unchanged original pushout inclusions. -/
def originalModelCategoryPushoutEqualizer (eff : EffectiveCofibrations V)
    {X Y : SequentialSpectrum V T} (f : X ⟶ Y) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    cofibrations (SequentialSpectrum V T) f →
      IsLimit (Fork.ofι f (pushout.condition (f := f) (g := f))) :=
  EnrichedProjective.MappedSources.sourceModelCategoryOriginalPushoutEqualizer d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf)) eff
    (SequentialSpectrum.EnrichedPresentation.enrichedEquivalence T) f

/-- The literal canonical sequential free source is uniformly small on its original I-cell chains. -/
theorem canonical_free_uniformlySmall
    (a : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T) (W : V)
    (hW : IsUniformlySmallRelativeTo.{w} d.I W) :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (generators T d.I)
      ((EnrichedFunctorCat.Free.functor a).obj W) := by
  let _ : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
    canonicalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.modelCategory_free_uniformlySmall d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf)) a W hW

/-- The original degree, actual free spectrum and original raw I-cell family remain unchanged. -/
theorem original_free_uniformlySmall (n : ℕ) (W : V)
    (hW : IsUniformlySmallRelativeTo.{w} d.I W) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((SequentialSpectrum.freeAt T n).obj W) := by
  let _ : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
  let _ : ∀ a : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T,
      PreservesColimitsOfSize.{w, w} (SequentialSpectrum.evaluation T a.degree) :=
    fun a => originalEvaluation_preservesColimitsOfSize T a.degree
  exact EnrichedProjective.MappedSources.sourceModelCategory_free_uniformlySmall d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf))
    (SequentialSpectrum.EnrichedPresentation.enrichedEquivalence T)
    (fun a => SequentialSpectrum.evaluation T a.degree) (originalEvaluationIso T)
    (fun a => SequentialSpectrum.freeAt T a.degree)
    (fun a => SequentialSpectrum.freeAtEvaluationAdjunction T a.degree)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree T n) W hW

/-- The actual raw free I domain retains the original compact source's smallness. -/
theorem original_free_I_domainSmall (hCell : CellularSource d) (n : ℕ) (i : d.I.toSet) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((SequentialSpectrum.freeAt T n).obj i.1.left) :=
  original_free_uniformlySmall T d hSourceI hSourceJ n i.1.left
    (CellularLocalizationSmallness.uniformly_small_of_compact hCell
      (hCell.I_domains_compact i))

/-- The actual raw free I codomain retains the original compact source's smallness. -/
theorem original_free_I_codomainSmall (hCell : CellularSource d) (n : ℕ) (i : d.I.toSet) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((SequentialSpectrum.freeAt T n).obj i.1.right) :=
  original_free_uniformlySmall T d hSourceI hSourceJ n i.1.right
    (CellularLocalizationSmallness.uniformly_small_of_compact hCell
      (hCell.I_codomains_compact i))

/-- The same raw free J domain is small without cofibrancy of that generating domain. -/
theorem original_free_J_domainSmall (hCell : CellularSource d) (n : ℕ) (j : d.J.toSet) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((SequentialSpectrum.freeAt T n).obj j.1.left) :=
  original_free_uniformlySmall T d hSourceI hSourceJ n j.1.left (hCell.J_domains_small j)

/-- The same raw free J codomain is small by the original noncofibrant-domain comparison. -/
theorem original_free_J_codomainSmall (hCell : CellularSource d) (n : ℕ) (j : d.J.toSet) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((SequentialSpectrum.freeAt T n).obj j.1.right) :=
  original_free_uniformlySmall T d hSourceI hSourceJ n j.1.right
    (CellularLocalizationSmallness.J_codomain_uniformly_small hCell j)


/-- Full cellularity of the same canonical sequential model at the original κ. -/
theorem canonicalCellularSource (hCell : CellularSource d) :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    CellularSource (canonicalGenerationData T d hSourceI hSourceJ) :=
  EnrichedProjective.MappedSources.modelCategory_cellularSource d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf)) hCell

/-- Full cellularity of the original raw sequential carrier and actual free I/J families. -/
theorem originalCellularSource (hCell : CellularSource d) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    CellularSource (originalGenerationData T d hSourceI hSourceJ) := by
  let _ : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
  let _ : ∀ a : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T,
      PreservesColimitsOfSize.{w, w} (SequentialSpectrum.evaluation T a.degree) :=
    fun a => originalEvaluation_preservesColimitsOfSize T a.degree
  exact EnrichedProjective.MappedSources.sourceModelCategory_cellularSource d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf)) hCell
    (SequentialSpectrum.EnrichedPresentation.enrichedEquivalence T)
    (fun a => SequentialSpectrum.evaluation T a.degree) (originalEvaluationIso T)
    (fun a => SequentialSpectrum.freeAt T a.degree)
    (fun a => SequentialSpectrum.freeAtEvaluationAdjunction T a.degree)

/-- Every actual canonical free source is compact on all original free-I presentations. -/
theorem canonical_free_cellularCompactAt (hCell : CellularSource d)
    {γ : Cardinal.{w}} (hγ : CellularLocalizationSmallness.commonCompactBound hCell ≤ γ)
    (a : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T) (W : V)
    (hW : IsCellularCompactAt.{w} d.I W γ) :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    IsCellularCompactAt.{w} (generators T d.I) ((EnrichedFunctorCat.Free.functor a).obj W) γ :=
  EnrichedProjective.MappedSources.modelCategory_free_cellularCompactAt d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf))
    hCell hγ a W hW

/-- The literal raw free spectrum is compact at the original source bound, on the same
original O, with its actual original occurrence and endpoint maps. -/
theorem original_free_cellularCompactAt (hCell : CellularSource d)
    {γ : Cardinal.{w}} (hγ : CellularLocalizationSmallness.commonCompactBound hCell ≤ γ)
    (n : ℕ) (W : V) (hW : IsCellularCompactAt.{w} d.I W γ) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    IsCellularCompactAt.{w} (originalGenerators T d.I) ((SequentialSpectrum.freeAt T n).obj W) γ := by
  let _ : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
  let _ : ∀ a : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T,
      PreservesColimitsOfSize.{w, w} (SequentialSpectrum.evaluation T a.degree) :=
    fun a => originalEvaluation_preservesColimitsOfSize T a.degree
  exact EnrichedProjective.MappedSources.sourceModelCategory_free_cellularCompactAt d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => indexHom_cofibration T a b f (baseI_cofibration d f hf)) hCell
    (SequentialSpectrum.EnrichedPresentation.enrichedEquivalence T)
    (fun a => SequentialSpectrum.evaluation T a.degree) (originalEvaluationIso T)
    (fun a => SequentialSpectrum.freeAt T a.degree)
    (fun a => SequentialSpectrum.freeAtEvaluationAdjunction T a.degree)
    hγ (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree T n) W hW

/-- The same canonical sequential model is left proper and cellular. -/
theorem canonicalModelCategory_isLeftProperCellular [hBaseProper : IsLeftProper V]
    (hCell : CellularSource d) :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    CellularSource (canonicalGenerationData T d hSourceI hSourceJ) ∧
      IsLeftProper (CategoryTheory.Spectra.Sequential.Spectrum T) := by
  let _ : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
    canonicalModelCategory T d hSourceI hSourceJ
  exact ⟨canonicalCellularSource T d hSourceI hSourceJ hCell,
    canonicalModelCategory_isLeftProper T d hSourceI hSourceJ⟩

/-- The same original raw sequential model is left proper and cellular. -/
theorem originalModelCategory_isLeftProperCellular [hBaseProper : IsLeftProper V]
    (hCell : CellularSource d) :
    letI : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
    CellularSource (originalGenerationData T d hSourceI hSourceJ) ∧ IsLeftProper (SequentialSpectrum V T) := by
  let _ : ModelCategory (SequentialSpectrum V T) := originalModelCategory T d hSourceI hSourceJ
  exact ⟨originalCellularSource T d hSourceI hSourceJ hCell,
    originalModelCategory_isLeftProper T d hSourceI hSourceJ⟩

end GenericSequentialLevel

namespace GenericSymmetricLevel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

omit [ModelCategory V] [IsClosedSymmetricMonoidalModelCategory V] [LocallySmall.{w} V] in
/-- Every actual ordinary sphere-module evaluation preserves the original working-size colimits. -/
theorem originalEvaluation_preservesColimitsOfSize (T : V) (a : I) :
    PreservesColimitsOfSize.{w, w} (genericSpectrumEvaluation T a) := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : PreservesColimitsOfSize.{w, w} (genericSphereOperatorEvaluation T a) := by
    change PreservesColimitsOfSize.{w, w} (EnrichedFunctorCat.evaluation (V := V) a)
    infer_instance
  exact preservesColimits_of_natIso (genericSphereModuleOperatorEvaluationIso T a)

variable (T : V) [IsCofibrant T] (d : CofibrantGenerationData V κ)
  (hSourceI : SourceCondition (κ := κ) T d.I)
  (hSourceJ : SourceCondition (κ := κ) T d.J)

include hSourceI hSourceJ

/-- The canonical operator free families retain the original generation cardinal and bottom. -/
def canonicalGenerationData :
    letI : ModelCategory (GenericSphereOperatorSpectra T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    CofibrantGenerationData (GenericSphereOperatorSpectra T) κ := by
  letI : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact EnrichedProjective.MappedSources.generationData d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ

/-- The actual canonical symmetric operator free I family is unchanged. -/
theorem canonicalGenerationData_I :
    letI : ModelCategory (GenericSphereOperatorSpectra T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    (canonicalGenerationData T d hSourceI hSourceJ).I = generators T d.I := rfl

/-- The actual canonical symmetric operator free J family is unchanged. -/
theorem canonicalGenerationData_J :
    letI : ModelCategory (GenericSphereOperatorSpectra T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    (canonicalGenerationData T d hSourceI hSourceJ).J = generators T d.J := rfl

/-- The exact ordinary free I/J families have generation data at the original cardinal and bottom. -/
def originalGenerationData :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    CofibrantGenerationData (SymmetricSpectrum (genericSphereDayMonoid T)) κ := by
  letI : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact EnrichedProjective.MappedSources.sourceGenerationData d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (genericSphereModuleOperatorEquivalence T)
    (fun a => genericSpectrumEvaluation T a) (genericSphereModuleOperatorEvaluationIso T)
    (fun a => genericSpectrumFreeAt T a) (fun a => genericSpectrumFreeAtEvaluationAdjunction T a)

/-- The unchanged original ordinary free I arrows are the recorded generating family. -/
theorem originalGenerationData_I :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    (originalGenerationData T d hSourceI hSourceJ).I = originalGenerators T d.I := rfl

/-- The unchanged original ordinary free J arrows are the recorded generating family. -/
theorem originalGenerationData_J :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    (originalGenerationData T d hSourceI hSourceJ).J = originalGenerators T d.J := rfl

/-- Every actual finite-index canonical symmetric cofibration is a regular monomorphism. -/
theorem canonicalModelCategory_cofibrations_regularMono (eff : EffectiveCofibrations V) :
    letI : ModelCategory (GenericSphereOperatorSpectra T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    cofibrations (GenericSphereOperatorSpectra T) ≤ regularMono (GenericSphereOperatorSpectra T) := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (GenericSphereOperatorSpectra T) :=
    canonicalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.modelCategory_cofibrations_regularMono d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf)) eff

/-- Every original ordinary sphere-module cofibration is a regular monomorphism. -/
theorem originalModelCategory_cofibrations_regularMono (eff : EffectiveCofibrations V) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    cofibrations (SymmetricSpectrum (genericSphereDayMonoid T)) ≤
      regularMono (SymmetricSpectrum (genericSphereDayMonoid T)) := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
    originalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.sourceModelCategory_cofibrations_regularMono d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf)) eff
    (genericSphereModuleOperatorEquivalence T)

/-- The exact ordinary sphere-module cofibration equalizes its actual original pushout pair. -/
def originalModelCategoryPushoutEqualizer (eff : EffectiveCofibrations V)
    {X Y : SymmetricSpectrum (genericSphereDayMonoid T)} (f : X ⟶ Y) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    cofibrations (SymmetricSpectrum (genericSphereDayMonoid T)) f →
      IsLimit (Fork.ofι f (pushout.condition (f := f) (g := f))) := by
  letI : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact EnrichedProjective.MappedSources.sourceModelCategoryOriginalPushoutEqualizer d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf)) eff
    (genericSphereModuleOperatorEquivalence T) f

/-- Canonical symmetric free sources are uniformly small on the same actual free I-cell family. -/
theorem canonical_free_uniformlySmall (a : I) (W : V)
    (hW : IsUniformlySmallRelativeTo.{w} d.I W) :
    letI : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
    letI : ModelCategory (GenericSphereOperatorSpectra T) :=
      canonicalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (generators T d.I)
      ((EnrichedFunctorCat.Free.functor (V := V) a).obj W) := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (GenericSphereOperatorSpectra T) :=
    canonicalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.modelCategory_free_uniformlySmall d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf)) a W hW

/-- The original finite index, ordinary free sphere module and all original cell maps are retained. -/
theorem original_free_uniformlySmall (a : I) (W : V)
    (hW : IsUniformlySmallRelativeTo.{w} d.I W) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((genericSpectrumFreeAt T a).obj W) := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
    originalModelCategory T d hSourceI hSourceJ
  let _ : ∀ a : I, PreservesColimitsOfSize.{w, w} (genericSpectrumEvaluation T a) :=
    fun a => originalEvaluation_preservesColimitsOfSize T a
  exact EnrichedProjective.MappedSources.sourceModelCategory_free_uniformlySmall d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf))
    (genericSphereModuleOperatorEquivalence T)
    (fun a => genericSpectrumEvaluation T a) (genericSphereModuleOperatorEvaluationIso T)
    (fun a => genericSpectrumFreeAt T a) (fun a => genericSpectrumFreeAtEvaluationAdjunction T a)
    a W hW

/-- The original ordinary free I domain retains the original compact source's smallness. -/
theorem original_free_I_domainSmall (hCell : CellularSource d) (a : I) (i : d.I.toSet) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((genericSpectrumFreeAt T a).obj i.1.left) :=
  original_free_uniformlySmall T d hSourceI hSourceJ a i.1.left
    (CellularLocalizationSmallness.uniformly_small_of_compact hCell
      (hCell.I_domains_compact i))

/-- The original ordinary free I codomain retains the original compact source's smallness. -/
theorem original_free_I_codomainSmall (hCell : CellularSource d) (a : I) (i : d.I.toSet) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((genericSpectrumFreeAt T a).obj i.1.right) :=
  original_free_uniformlySmall T d hSourceI hSourceJ a i.1.right
    (CellularLocalizationSmallness.uniformly_small_of_compact hCell
      (hCell.I_codomains_compact i))

/-- The original ordinary free J domain is small with its actual noncofibrant source. -/
theorem original_free_J_domainSmall (hCell : CellularSource d) (a : I) (j : d.J.toSet) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((genericSpectrumFreeAt T a).obj j.1.left) :=
  original_free_uniformlySmall T d hSourceI hSourceJ a j.1.left (hCell.J_domains_small j)

/-- The original ordinary free J codomain is small by its original source comparison. -/
theorem original_free_J_codomainSmall (hCell : CellularSource d) (a : I) (j : d.J.toSet) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    IsUniformlySmallRelativeTo.{w} (originalGenerators T d.I)
      ((genericSpectrumFreeAt T a).obj j.1.right) :=
  original_free_uniformlySmall T d hSourceI hSourceJ a j.1.right
    (CellularLocalizationSmallness.J_codomain_uniformly_small hCell j)


/-- Full cellularity of the same canonical symmetric operator model at original κ. -/
theorem canonicalCellularSource (hCell : CellularSource d) :
    letI : ModelCategory (GenericSphereOperatorSpectra T) := canonicalModelCategory T d hSourceI hSourceJ
    CellularSource (canonicalGenerationData T d hSourceI hSourceJ) := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (GenericSphereOperatorSpectra T) := canonicalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.modelCategory_cellularSource d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf)) hCell

/-- Full cellularity of the original ordinary S(T)-module model and its actual free families. -/
theorem originalCellularSource (hCell : CellularSource d) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    CellularSource (originalGenerationData T d hSourceI hSourceJ) := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
    originalModelCategory T d hSourceI hSourceJ
  let _ : ∀ a : I, PreservesColimitsOfSize.{w, w} (genericSpectrumEvaluation T a) :=
    fun a => originalEvaluation_preservesColimitsOfSize T a
  exact EnrichedProjective.MappedSources.sourceModelCategory_cellularSource d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf)) hCell
    (genericSphereModuleOperatorEquivalence T)
    (fun a => genericSpectrumEvaluation T a) (genericSphereModuleOperatorEvaluationIso T)
    (fun a => genericSpectrumFreeAt T a) (fun a => genericSpectrumFreeAtEvaluationAdjunction T a)

/-- The literal canonical symmetric free source is compact on every original free-I history. -/
theorem canonical_free_cellularCompactAt (hCell : CellularSource d)
    {γ : Cardinal.{w}} (hγ : CellularLocalizationSmallness.commonCompactBound hCell ≤ γ)
    (a : I) (W : V) (hW : IsCellularCompactAt.{w} d.I W γ) :
    letI : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
    letI : ModelCategory (GenericSphereOperatorSpectra T) := canonicalModelCategory T d hSourceI hSourceJ
    IsCellularCompactAt.{w} (generators T d.I) ((EnrichedFunctorCat.Free.functor (V := V) a).obj W) γ := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (GenericSphereOperatorSpectra T) := canonicalModelCategory T d hSourceI hSourceJ
  exact EnrichedProjective.MappedSources.modelCategory_free_cellularCompactAt d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf)) hCell hγ a W hW

/-- The original ordinary free S(T)-module keeps full compactness at the original source
bound, with the same original ordinal, occurrences, coefficients and endpoint maps. -/
theorem original_free_cellularCompactAt (hCell : CellularSource d)
    {γ : Cardinal.{w}} (hγ : CellularLocalizationSmallness.commonCompactBound hCell ≤ γ)
    (a : I) (W : V) (hW : IsCellularCompactAt.{w} d.I W γ) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    IsCellularCompactAt.{w} (originalGenerators T d.I) ((genericSpectrumFreeAt T a).obj W) γ := by
  let _ : EnrichedCategory V I := CategoryTheory.Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let _ : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
    originalModelCategory T d hSourceI hSourceJ
  let _ : ∀ a : I, PreservesColimitsOfSize.{w, w} (genericSpectrumEvaluation T a) :=
    fun a => originalEvaluation_preservesColimitsOfSize T a
  exact EnrichedProjective.MappedSources.sourceModelCategory_free_cellularCompactAt d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (fun a b {_ _} f hf => CategoryTheory.Spectra.Symmetric.LevelGenerators.homTensor_cofibration
      T a b f (GenericSequentialLevel.baseI_cofibration d f hf)) hCell
    (genericSphereModuleOperatorEquivalence T)
    (fun a => genericSpectrumEvaluation T a) (genericSphereModuleOperatorEvaluationIso T)
    (fun a => genericSpectrumFreeAt T a) (fun a => genericSpectrumFreeAtEvaluationAdjunction T a)
    hγ a W hW

/-- The same canonical symmetric operator model is left proper and cellular. -/
theorem canonicalModelCategory_isLeftProperCellular [hBaseProper : IsLeftProper V]
    (hCell : CellularSource d) :
    letI : ModelCategory (GenericSphereOperatorSpectra T) := canonicalModelCategory T d hSourceI hSourceJ
    CellularSource (canonicalGenerationData T d hSourceI hSourceJ) ∧
      IsLeftProper (GenericSphereOperatorSpectra T) := by
  let _ : ModelCategory (GenericSphereOperatorSpectra T) := canonicalModelCategory T d hSourceI hSourceJ
  exact ⟨canonicalCellularSource T d hSourceI hSourceJ hCell,
    canonicalModelCategory_isLeftProper T d hSourceI hSourceJ⟩

/-- The actual ordinary S(T)-module model is left proper and cellular. -/
theorem originalModelCategory_isLeftProperCellular [hBaseProper : IsLeftProper V]
    (hCell : CellularSource d) :
    letI : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
      originalModelCategory T d hSourceI hSourceJ
    CellularSource (originalGenerationData T d hSourceI hSourceJ) ∧
      IsLeftProper (SymmetricSpectrum (genericSphereDayMonoid T)) := by
  let _ : ModelCategory (SymmetricSpectrum (genericSphereDayMonoid T)) :=
    originalModelCategory T d hSourceI hSourceJ
  exact ⟨originalCellularSource T d hSourceI hSourceJ hCell,
    originalModelCategory_isLeftProper T d hSourceI hSourceJ⟩

end GenericSymmetricLevel

end HomotopicalAlgebra

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.GenericLevelGenerators
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveMappedFactors

/-!
# Actual projective level models on the original generic sequential carrier

All original free images and evaluated cell source-Hom witnesses remain
at the caller's regular cardinal and ordinal bottom. Tensor-power generator
classes are derived from cofT, with the empty power handled by unitors.
The target model, all five classes and its original free Quillen adjunctions
are constructed on the existing canonical sequential carrier.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uV vV

open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory

namespace HomotopicalAlgebra.GenericSequentialLevel

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [ModelCategory V]

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The original level property is evaluated at every actual natural-number degree. -/
def levelProperty (T : V) (P : MorphismProperty V) :
    MorphismProperty (CategoryTheory.Spectra.Sequential.Spectrum T) :=
  EvaluationTransfer.evaluationProperty
    (fun n : ℕ => CategoryTheory.Spectra.Sequential.evaluation T n) P

/-- The original generator family consists of every literal free image with its original source label. -/
abbrev generators (T : V) (P : MorphismProperty V) :
    MorphismProperty (CategoryTheory.Spectra.Sequential.Spectrum T) :=
  EnrichedProjective.generators (A := CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T) P

/-- Every original base generator and natural degree occur in the actual literal free family. -/
theorem generator_mem (T : V) (P : MorphismProperty V) (n : ℕ) {X Y : V} (f : X ⟶ Y) (hf : P f) :
    generators T P ((CategoryTheory.Spectra.Sequential.freeAt T n).map f) := by
  apply (adjointFamilyGenerators_iff
    (fun a : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T => EnrichedFunctorCat.Free.functor a)
    P _).mpr
  exact ⟨⟨CategoryTheory.SequentialSpectrum.EnrichedIndex.degree T n, ⟨Arrow.mk f, hf⟩⟩, rfl⟩

/-- All original degree objects and natural labels give the same complete evaluated property. -/
theorem evaluationProperty_eq (T : V) (P : MorphismProperty V) :
    EvaluationTransfer.evaluationProperty
        (fun a : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T => EnrichedFunctorCat.evaluation a) P =
      levelProperty T P := by
  ext X Y f
  rw [EvaluationTransfer.evaluationProperty_iff, levelProperty, EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h n
    exact h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree T n)
  · intro h a
    rcases a with ⟨n⟩
    exact h n

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]

/-- The original source-Hom requirement on the actual evaluated free-cell chains. -/
abbrev SourceCondition (T : V) (P : MorphismProperty V) :=
  EnrichedProjective.MappedSources.SourceCondition
    (A := CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T) (κ := κ) P

omit [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V] in
/-- Every original base I generator belongs to the original base cofibration class. -/
theorem baseI_cofibration (d : CofibrantGenerationData V κ) {X Y : V} (f : X ⟶ Y) (hf : d.I f) :
    cofibrations V f := by
  have h : d.I.rlp.llp = cofibrations V := by rw [d.I_rlp, trivialFibrations_llp V]
  exact (d.I.le_llp_rlp.trans h.le) f hf

omit [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V] in
/-- Every original base J generator belongs to the original base trivial-cofibration class. -/
theorem baseJ_trivialCofibration (d : CofibrantGenerationData V κ) {X Y : V} (f : X ⟶ Y) (hf : d.J f) :
    trivialCofibrations V f := by
  have h : d.J.rlp.llp = trivialCofibrations V := by rw [d.J_rlp, fibrations_llp V]
  exact (d.J.le_llp_rlp.trans h.le) f hf

variable [IsClosedSymmetricMonoidalModelCategory V]
  (T : V) [IsCofibrant T] (d : CofibrantGenerationData V κ)
  (hSourceI : SourceCondition (κ := κ) T d.I) (hSourceJ : SourceCondition (κ := κ) T d.J)

omit [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V] in
/-- CofT derives the complete coefficient bound for every original free J generator. -/
theorem generatorsJ_tensor_trivialCofibration
    (a b : CategoryTheory.SequentialSpectrum.EnrichedIndex.Index T) {X Y : V} (f : X ⟶ Y) (hf : d.J f) :
    trivialCofibrations V (f ▷ (a ⟶[V] b)) :=
  indexHom_trivialCofibration T a b f (baseJ_trivialCofibration d f hf)

/-- The actual projective model is constructed on the existing canonical sequential T carrier. -/
@[instance_reducible]
def canonicalModelCategory : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) :=
  EnrichedProjective.MappedSources.modelCategory d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ

/-- The actual weak equivalences are exactly all original level weak equivalences. -/
theorem weakEquivalences_eq :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) := canonicalModelCategory T d hSourceI hSourceJ
    weakEquivalences (CategoryTheory.Spectra.Sequential.Spectrum T) = levelProperty T (weakEquivalences V) := by
  let _ : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) := canonicalModelCategory T d hSourceI hSourceJ
  exact (EnrichedProjective.MappedSources.weakEquivalences_eq d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ).trans (evaluationProperty_eq T _)

/-- The actual cofibrations are generated by every original literal free I image. -/
theorem cofibrations_eq :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) := canonicalModelCategory T d hSourceI hSourceJ
    cofibrations (CategoryTheory.Spectra.Sequential.Spectrum T) = (generators T d.I).rlp.llp :=
  EnrichedProjective.MappedSources.cofibrations_eq d (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ

/-- The actual fibrations are exactly all original level fibrations. -/
theorem fibrations_eq :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) := canonicalModelCategory T d hSourceI hSourceJ
    fibrations (CategoryTheory.Spectra.Sequential.Spectrum T) = levelProperty T (fibrations V) := by
  let _ : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) := canonicalModelCategory T d hSourceI hSourceJ
  exact (EnrichedProjective.MappedSources.fibrations_eq d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ).trans (evaluationProperty_eq T _)

/-- The actual trivial fibrations are exactly all original level trivial fibrations. -/
theorem trivialFibrations_eq :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) := canonicalModelCategory T d hSourceI hSourceJ
    trivialFibrations (CategoryTheory.Spectra.Sequential.Spectrum T) = levelProperty T (trivialFibrations V) := by
  let _ : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) := canonicalModelCategory T d hSourceI hSourceJ
  exact (EnrichedProjective.MappedSources.trivialFibrations_eq d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ).trans (evaluationProperty_eq T _)

/-- The actual trivial cofibrations are generated by every original literal free J image. -/
theorem trivialCofibrations_eq :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) := canonicalModelCategory T d hSourceI hSourceJ
    trivialCofibrations (CategoryTheory.Spectra.Sequential.Spectrum T) = (generators T d.J).rlp.llp :=
  EnrichedProjective.MappedSources.trivialCofibrations_eq d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ

/-- Every original canonical sequential free/evaluation adjunction is Quillen for this same model. -/
theorem freeAtEvaluation_isQuillenAdjunction (n : ℕ) :
    letI : ModelCategory (CategoryTheory.Spectra.Sequential.Spectrum T) := canonicalModelCategory T d hSourceI hSourceJ
    (CategoryTheory.Spectra.Sequential.freeAtEvaluationAdjunction T n).IsQuillenAdjunction :=
  EnrichedProjective.MappedSources.freeAtEvaluation_isQuillenAdjunction d
    (generatorsJ_tensor_trivialCofibration T d) hSourceI hSourceJ
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree T n)

end HomotopicalAlgebra.GenericSequentialLevel

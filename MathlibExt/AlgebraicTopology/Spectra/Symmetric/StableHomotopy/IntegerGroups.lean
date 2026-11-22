/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialIndexOmegaTransport
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerOmegaRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKLocalReplacement

/-!
# Original integer homotopy groups of actual native symmetric spectra

The original enriched restriction along the sequential-to-symmetric index
embedding supplies the underlying sequential prespectrum. Its existing
changing-degree group diagrams and chosen filtered group colimits define
every integer homotopy group. Restriction retains the level objects and
input morphism components at embedded indices, with the sequential
enriched actions induced by the embedding.

On genuine native Omega objects these groups detect the original level
weak equivalences. An arbitrary symmetric stable-equivalence converse
requires its semistability hypothesis and is not asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
namespace SymmetricIntegerHomotopy

open CategoryTheory.Spectra.SpectrumIndexMaps
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerOmegaRecognitionGeometry
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

/-- The underlying sequential prespectrum restricts enriched actions along
the original sequential-to-symmetric index embedding. -/
abbrev underlyingSequential : SymmetricCarrier.{u, v} ⥤ PointedCGWH.SequentialSpectrum.{u, v} :=
  EnrichedFunctorCat.restriction sequentialSymmetricOperatorIndexFunctor.{u, v}

/-- Every original underlying level is the same actual symmetric-index value. -/
theorem underlying_level (X : SymmetricCarrier.{u, v}) (n : ℕ) :
    (underlyingSequential.obj X).level n = X.toEnrichedFunctor.obj (symmetricDegree n) := rfl

/-- Every whole original input arrow retains its actual symmetric-index component. -/
theorem underlying_map {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap (underlyingSequential.map f) n =
      EnrichedFunctorCat.component f (symmetricDegree n) :=
  EnrichedFunctorCat.restrictionMap_component sequentialSymmetricOperatorIndexFunctor f
    (sequentialDegree n)

/-- The actual integer diagonal retains the original positive group degree and original level. -/
def integerDiagonalFunctor (q : ℤ) : SymmetricCarrier.{u, v} ⥤ (ℕ ⥤ GrpCat.{v}) :=
  underlyingSequential ⋙ integerDiagonalDiagramFunctor q

/-- The actual original positive stage group is evaluated at the original symmetric level. -/
theorem integerDiagonalFunctor_obj_stage (q : ℤ) (X : SymmetricCarrier.{u, v}) (n : ℕ) :
    ((integerDiagonalFunctor q).obj X).obj n =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).obj
        (X.toEnrichedFunctor.obj (symmetricDegree (integerTailLevel q + n))) := rfl

/-- Every original stage map is the actual positive group map of the native input component. -/
theorem integerDiagonalFunctor_map_stage (q : ℤ) {X Y : SymmetricCarrier.{u, v}}
    (f : X ⟶ Y) (n : ℕ) :
    ((integerDiagonalFunctor q).map f).app n =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (EnrichedFunctorCat.component f (symmetricDegree (integerTailLevel q + n))) :=
  congrArg ((PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map)
    (underlying_map f (integerTailLevel q + n))

/-- Every integer group uses the canonical sequential functor on the full original restriction. -/
def integerPiFunctor (q : ℤ) : SymmetricCarrier.{u, v} ⥤ GrpCat.{v} :=
  underlyingSequential ⋙ IntegerStablePiGeometry.integerStablePiFunctor q

/-- Every whole native input map acts by the same original group quotient map. -/
theorem integerPiFunctor_map (q : ℤ) {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    (integerPiFunctor q).map f =
      GrpCat.FilteredColimits.colimitMap ((integerDiagonalFunctor q).map f) := rfl

/-- The original positive tail represents the specified integer degree at every stage. -/
theorem integerPi_stage_degree (q : ℤ) (n : ℕ) :
    ((integerTailPositiveIndex q + n + 1 : ℕ) : ℤ) -
      ((integerTailLevel q + n : ℕ) : ℤ) = q :=
  integerTail_degree q n

/-- The actual native symmetric stage leg is the original chosen group quotient leg. -/
def integerPiLeg (q : ℤ) (X : SymmetricCarrier.{u, v}) (n : ℕ) :
    (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).obj
      ((underlyingSequential.obj X).level (integerTailLevel q + n)) ⟶
        (integerPiFunctor q).obj X :=
  integerStablePiLeg q (underlyingSequential.obj X) n

/-- All original stage maps and both actual native endpoints participate in naturality. -/
theorem integerPiLeg_naturality (q : ℤ) {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    integerPiLeg q X n ≫ (integerPiFunctor q).map f =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (PointedCGWH.SequentialSpectrum.levelMap (underlyingSequential.map f)
          (integerTailLevel q + n)) ≫ integerPiLeg q Y n :=
  integerStablePiLeg_naturality q (underlyingSequential.map f) n

/-- The same quotient leg is natural under the full original symmetric component map. -/
theorem integerPiLeg_naturality_component (q : ℤ) {X Y : SymmetricCarrier.{u, v}}
    (f : X ⟶ Y) (n : ℕ) :
    integerPiLeg q X n ≫ (integerPiFunctor q).map f =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (EnrichedFunctorCat.component f (symmetricDegree (integerTailLevel q + n))) ≫
          integerPiLeg q Y n := by
  rw [integerPiLeg_naturality, underlying_map]

/-- The actual naive integer criterion uses all original integer group maps. -/
def integerPiStarEquivalences : MorphismProperty SymmetricCarrier.{u, v} :=
  IntegerStablePiGeometry.integerPiStarEquivalences.inverseImage underlyingSequential

/-- The complete native naive criterion retains every integer and every original input arrow. -/
theorem integerPiStarEquivalences_iff {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences f ↔ ∀ q : ℤ, IsIso ((integerPiFunctor q).map f) :=
  IntegerStablePiGeometry.integerPiStarEquivalences_iff (underlyingSequential.map f)

/-- The full original restriction preserves exactly these same original integer group maps. -/
theorem integerPiStarEquivalences_iff_underlying {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences f ↔
      IntegerStablePiGeometry.integerPiStarEquivalences
        (underlyingSequential.map f) :=
  MorphismProperty.inverseImage_iff
    IntegerStablePiGeometry.integerPiStarEquivalences underlyingSequential f

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Every native symmetric object is an original sequential level,
so level weakness is reflected. -/
theorem underlying_levelWeak_iff {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (underlyingSequential.map f) ↔
      weakEquivalences SymmetricCarrier.{u, v} f := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq
      (A := PointedCGWH.Spectra.Sequential.Index.{u, v}),
    HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v}),
    EvaluationTransfer.evaluationProperty_iff, EvaluationTransfer.evaluationProperty_iff]
  change (∀ a : PointedCGWH.Spectra.Sequential.Index.{u, v},
      weakEquivalences PointedCGWH.{u, v}
        (EnrichedFunctorCat.component
          (EnrichedFunctorCat.restrictionMap sequentialSymmetricOperatorIndexFunctor f) a)) ↔
    ∀ a : PointedCGWH.SymmetricOperatorIndex.{u, v},
      weakEquivalences PointedCGWH.{u, v} (EnrichedFunctorCat.component f a)
  simp only [EnrichedFunctorCat.restrictionMap_component]
  constructor
  · intro h a
    rcases a with ⟨⟨⟨n⟩⟩⟩
    exact h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)
  · intro h a
    exact h (sequentialSymmetricOperatorIndexFunctor.obj a)

/-- Original native level weak maps induce isomorphisms on all these integer groups. -/
theorem levelWeak_le_integerPiStarEquivalences {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences SymmetricCarrier.{u, v} f) : integerPiStarEquivalences f :=
  (integerPiStarEquivalences_iff_underlying f).mpr
    (StageIntegerStablePiGeometry.levelWeak_le_integerPiStarEquivalences
      (underlyingSequential.map f) ((underlying_levelWeak_iff f).mpr hf))

/-- The actual native Omega hypotheses give integer detection of the same original level class. -/
theorem integerPiStar_iff_levelWeak_of_isOmega
    {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hX : NativeK.IsOmega symmetricFamily X) (hY : NativeK.IsOmega symmetricFamily Y) :
    integerPiStarEquivalences f ↔ weakEquivalences SymmetricCarrier.{u, v} f :=
  (integerPiStarEquivalences_iff_underlying f).trans
    ((omegaMap_integerPiStar_iff_modelWeak (underlyingSequential.map f)
      ((sequentialSymmetric_isOmega_iff X).mpr hX)
      ((sequentialSymmetric_isOmega_iff Y).mpr hY)).trans (underlying_levelWeak_iff f))

/-- Between original native Omega spectra, the actual local Hom tests
equal the integer criterion. -/
theorem localTests_iff_integerPiStar_of_isOmega
    {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hX : NativeK.IsOmega symmetricFamily X) (hY : NativeK.IsOmega symmetricFamily Y) :
    NativeK.localTestEquivalences symmetricFamily f ↔ integerPiStarEquivalences f :=
  (NativeK.localTestEquivalences_iff_levelWeak_of_local symmetricFamily f
    ((NativeK.lifting_toZero_iff_isOmega symmetricFamily X).mpr hX)
    ((NativeK.lifting_toZero_iff_isOmega symmetricFamily Y).mpr hY)).trans
      (integerPiStar_iff_levelWeak_of_isOmega f hX hY).symm

end SymmetricIntegerHomotopy
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.StableHomotopy.IntegerGroups

/-!
# Original integer homotopy groups of actual native orthogonal spectra

The original composite enriched index embedding supplies the restriction
to an underlying sequential prespectrum. Restriction retains the
orthogonal level objects and input morphism components at embedded
indices, with the sequential enriched actions induced by the embedding.
The prespectrum's actual group diagrams and filtered colimits define every
integer homotopy group with the original level and map formulas.

On original native Omega objects these groups detect the original level
weak equivalences. The arbitrary-source stable criterion remains a
separate result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
namespace OrthogonalIntegerHomotopy

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
the original composite sequential-to-orthogonal index embedding. -/
abbrev underlyingSequential : OrthogonalCarrier.{u, v} ⥤ PointedCGWH.SequentialSpectrum.{u, v} :=
  EnrichedFunctorCat.restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}

/-- Every original underlying level is the actual orthogonal value at that dimension. -/
theorem underlying_level (X : OrthogonalCarrier.{u, v}) (n : ℕ) :
    (underlyingSequential.obj X).level n =
      X.toEnrichedFunctor.obj (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) := rfl

/-- The whole original input map retains its actual orthogonal component. -/
theorem underlying_map {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap (underlyingSequential.map f) n =
      EnrichedFunctorCat.component f (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n) :=
  EnrichedFunctorCat.restrictionMap_component sequentialOrthogonalOperatorIndexFunctor f
    (sequentialDegree n)

/-- The actual integer diagram retains the original varying homotopy degree and original level. -/
def integerDiagonalFunctor (q : ℤ) : OrthogonalCarrier.{u, v} ⥤ (ℕ ⥤ GrpCat.{v}) :=
  underlyingSequential ⋙ integerDiagonalDiagramFunctor q

/-- All original positive stage groups are evaluated at their actual orthogonal dimensions. -/
theorem integerDiagonalFunctor_obj_stage (q : ℤ) (X : OrthogonalCarrier.{u, v}) (n : ℕ) :
    ((integerDiagonalFunctor q).obj X).obj n =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).obj
        (X.toEnrichedFunctor.obj (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex
          (integerTailLevel q + n))) := rfl

/-- Every complete native stage map is the group map of the original orthogonal component. -/
theorem integerDiagonalFunctor_map_stage (q : ℤ) {X Y : OrthogonalCarrier.{u, v}}
    (f : X ⟶ Y) (n : ℕ) :
    ((integerDiagonalFunctor q).map f).app n =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (EnrichedFunctorCat.component f (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex
          (integerTailLevel q + n))) :=
  congrArg ((PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map)
    (underlying_map f (integerTailLevel q + n))

/-- Every integer group uses the canonical sequential functor on the full original restriction. -/
def integerPiFunctor (q : ℤ) : OrthogonalCarrier.{u, v} ⥤ GrpCat.{v} :=
  underlyingSequential ⋙ IntegerStablePiGeometry.integerStablePiFunctor q

/-- The actual original group quotient map retains the entire original input arrow. -/
theorem integerPiFunctor_map (q : ℤ) {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    (integerPiFunctor q).map f =
      GrpCat.FilteredColimits.colimitMap ((integerDiagonalFunctor q).map f) := rfl

/-- Every original positive stage has the actual specified integer degree. -/
theorem integerPi_stage_degree (q : ℤ) (n : ℕ) :
    ((integerTailPositiveIndex q + n + 1 : ℕ) : ℤ) -
      ((integerTailLevel q + n : ℕ) : ℤ) = q :=
  integerTail_degree q n

/-- The native orthogonal stage leg is the same original chosen group quotient leg. -/
def integerPiLeg (q : ℤ) (X : OrthogonalCarrier.{u, v}) (n : ℕ) :
    (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).obj
      ((underlyingSequential.obj X).level (integerTailLevel q + n)) ⟶
        (integerPiFunctor q).obj X :=
  integerStablePiLeg q (underlyingSequential.obj X) n

/-- Every actual original group leg retains all original input map naturalities. -/
theorem integerPiLeg_naturality (q : ℤ) {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    integerPiLeg q X n ≫ (integerPiFunctor q).map f =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (PointedCGWH.SequentialSpectrum.levelMap (underlyingSequential.map f)
          (integerTailLevel q + n)) ≫ integerPiLeg q Y n :=
  integerStablePiLeg_naturality q (underlyingSequential.map f) n

/-- All original quotient legs keep their actual native orthogonal component maps. -/
theorem integerPiLeg_naturality_component (q : ℤ) {X Y : OrthogonalCarrier.{u, v}}
    (f : X ⟶ Y) (n : ℕ) :
    integerPiLeg q X n ≫ (integerPiFunctor q).map f =
      (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (EnrichedFunctorCat.component f (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex
          (integerTailLevel q + n))) ≫ integerPiLeg q Y n := by
  rw [integerPiLeg_naturality, underlying_map]

/-- The original integer criterion tests every actual integer group map. -/
def integerPiStarEquivalences : MorphismProperty OrthogonalCarrier.{u, v} :=
  IntegerStablePiGeometry.integerPiStarEquivalences.inverseImage underlyingSequential

/-- Every original integer and entire original native arrow participates in this criterion. -/
theorem integerPiStarEquivalences_iff {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences f ↔ ∀ q : ℤ, IsIso ((integerPiFunctor q).map f) :=
  IntegerStablePiGeometry.integerPiStarEquivalences_iff (underlyingSequential.map f)

/-- The original full restriction keeps exactly the same all-integer group maps. -/
theorem integerPiStarEquivalences_iff_underlying {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences f ↔
      IntegerStablePiGeometry.integerPiStarEquivalences (underlyingSequential.map f) :=
  MorphismProperty.inverseImage_iff
    IntegerStablePiGeometry.integerPiStarEquivalences underlyingSequential f

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- All original orthogonal dimensions occur in the original sequential restriction. -/
theorem underlying_levelWeak_iff {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (underlyingSequential.map f) ↔
      weakEquivalences OrthogonalCarrier.{u, v} f := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq
      (A := PointedCGWH.Spectra.Sequential.Index.{u, v}),
    HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq
      (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}),
    EvaluationTransfer.evaluationProperty_iff, EvaluationTransfer.evaluationProperty_iff]
  change (∀ a : PointedCGWH.Spectra.Sequential.Index.{u, v},
      weakEquivalences PointedCGWH.{u, v}
        (EnrichedFunctorCat.component
          (EnrichedFunctorCat.restrictionMap sequentialOrthogonalOperatorIndexFunctor f) a)) ↔
    ∀ a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v},
      weakEquivalences PointedCGWH.{u, v} (EnrichedFunctorCat.component f a)
  simp only [EnrichedFunctorCat.restrictionMap_component]
  constructor
  · intro h a
    rcases a with ⟨n⟩
    exact h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)
  · intro h a
    exact h (sequentialOrthogonalOperatorIndexFunctor.obj a)

/-- Original native level weak maps preserve every integer homotopy group. -/
theorem levelWeak_le_integerPiStarEquivalences {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences OrthogonalCarrier.{u, v} f) : integerPiStarEquivalences f :=
  (integerPiStarEquivalences_iff_underlying f).mpr
    (StageIntegerStablePiGeometry.levelWeak_le_integerPiStarEquivalences
      (underlyingSequential.map f) ((underlying_levelWeak_iff f).mpr hf))

/-- All original native Omega labels give integer detection of the unchanged level weak class. -/
theorem integerPiStar_iff_levelWeak_of_isOmega
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hX : NativeK.IsOmega orthogonalFamily X) (hY : NativeK.IsOmega orthogonalFamily Y) :
    integerPiStarEquivalences f ↔ weakEquivalences OrthogonalCarrier.{u, v} f :=
  (integerPiStarEquivalences_iff_underlying f).trans
    ((omegaMap_integerPiStar_iff_modelWeak (underlyingSequential.map f)
      ((sequentialOrthogonal_isOmega_iff X).mpr hX)
      ((sequentialOrthogonal_isOmega_iff Y).mpr hY)).trans (underlying_levelWeak_iff f))

/-- The actual native Omega-target Hom tests equal this integer criterion on Omega endpoints. -/
theorem localTests_iff_integerPiStar_of_isOmega
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hX : NativeK.IsOmega orthogonalFamily X) (hY : NativeK.IsOmega orthogonalFamily Y) :
    NativeK.localTestEquivalences orthogonalFamily f ↔ integerPiStarEquivalences f :=
  (NativeK.localTestEquivalences_iff_levelWeak_of_local orthogonalFamily f
    ((NativeK.lifting_toZero_iff_isOmega orthogonalFamily X).mpr hX)
    ((NativeK.lifting_toZero_iff_isOmega orthogonalFamily Y).mpr hY)).trans
      (integerPiStar_iff_levelWeak_of_isOmega f hX hY).symm

end OrthogonalIntegerHomotopy
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual

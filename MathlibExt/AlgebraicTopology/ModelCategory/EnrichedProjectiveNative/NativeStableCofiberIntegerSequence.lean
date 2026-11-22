/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.IntegerExactSequence
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerExactness
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberIntegerExactness
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.StableHomotopy.IntegerGroups
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerGroups

/-!
# The full original integer cofiber sequence functors

Every raw spectrum arrow gives a full integer graded exact group sequence.
Its source differential is the original integer map, its inclusion uses
the original Q counit inverse and I-cone pushout, and its connection is the
original chosen boundary followed by the scalar suspension inverse.

Whole arrow squares act through both original components and the complete
chosen cofiber map. The original all-integer exactness and null-composite
theorems supply the sequence fields; they are not caller hypotheses.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open GrpCat.IntegerSequence
open scoped CGWH.modelCategory

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerSequence

open HomotopicalAlgebra.EnrichedProjective.Native
open NativeStableCofiberIntegerMaps NativeStableCofiberIntegerExactness

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (j : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I)

/-- The unchanged original native integer groups at all three positions. -/
def term (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) : Index → GrpCat.{v}
  | (q, .source) => (integerPiFunctor j q).obj F.left
  | (q, .target) => (integerPiFunctor j q).obj F.right
  | (q, .cofiber) => (integerPiFunctor j q).obj ((cofiber (B := B) (I := I)).obj F)

/-- Each original leg retains its entire homomorphism and its literal integer degree. -/
def differential (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    ∀ i, term j F i ⟶ term j F (next i)
  | (q, .source) => (integerPiFunctor j q).map F.hom
  | (q, .target) => inclusionInteger (j := j) q F
  | (q, .cofiber) => connecting (j := j) q F

/-- The complete original I-Q cofiber sequence, exact at every integer position. -/
def sequence (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    GrpCat.IntegerExactSequence.{v} where
  term := term j F
  differential := differential j F
  differential_comp i := by
    rcases i with ⟨q, p⟩
    cases p with
    | source =>
      apply GrpCat.hom_ext
      ext x
      exact source_inclusion_null (j := j) q F x
    | target =>
      apply GrpCat.hom_ext
      ext x
      exact inclusion_connecting_null (j := j) q F x
    | cofiber =>
      apply GrpCat.hom_ext
      ext x
      exact connecting_source_null (j := j) q F x
  exact i := by
    rcases i with ⟨q, p⟩
    cases p with
    | source => exact source_inclusion_mulExact (j := j) q F
    | target => exact inclusion_connecting_mulExact (j := j) q F
    | cofiber => exact connecting_source_mulExact (j := j) q F

/-- A whole native arrow square acts on all original source, target and cofiber groups. -/
def map {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (m : F ⟶ G) :
    sequence j F ⟶ sequence j G where
  app i := match i with
    | (q, .source) => (integerPiFunctor j q).map m.left
    | (q, .target) => (integerPiFunctor j q).map m.right
    | (q, .cofiber) => (integerPiFunctor j q).map ((cofiber (B := B) (I := I)).map m)
  comm i := by
    rcases i with ⟨q, p⟩
    cases p with
    | source => exact (sourceIntegerNatTrans (j := j) q).naturality m
    | target => exact inclusionInteger_naturality (j := j) q m
    | cofiber => exact connecting_naturality (j := j) q m

/-- The actual functor on all raw native arrows and their complete two-component squares. -/
def cofiberSequenceFunctor :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤ GrpCat.IntegerExactSequence.{v} where
  obj F := sequence j F
  map m := map j m
  map_id F := by
    apply GrpCat.IntegerExactSequence.Hom.ext
    rintro ⟨q, p⟩
    cases p <;> simp [map, sequence, term]
  map_comp m n := by
    apply GrpCat.IntegerExactSequence.Hom.ext
    rintro ⟨q, p⟩
    cases p <;> simp [map, sequence, term]

/-- The source position is the unchanged original native integer group. -/
theorem cofiberSequenceFunctor_source
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (q : ℤ) :
    ((cofiberSequenceFunctor j).obj F).term (q, .source) =
      (integerPiFunctor j q).obj F.left := rfl

/-- The target position is the unchanged original native integer group. -/
theorem cofiberSequenceFunctor_target
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (q : ℤ) :
    ((cofiberSequenceFunctor j).obj F).term (q, .target) =
      (integerPiFunctor j q).obj F.right := rfl

/-- The cofiber position is the integer group of the original I-Q pushout. -/
theorem cofiberSequenceFunctor_cofiber
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (q : ℤ) :
    ((cofiberSequenceFunctor j).obj F).term (q, .cofiber) =
      (integerPiFunctor j q).obj ((cofiber (B := B) (I := I)).obj F) := rfl

/-- The source differential is the whole original native integer map. -/
theorem cofiberSequenceFunctor_source_differential
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (q : ℤ) :
    ((cofiberSequenceFunctor j).obj F).differential (q, .source) =
      (integerPiFunctor j q).map F.hom := rfl

/-- The target differential retains the original Q inverse and actual pushout inclusion. -/
theorem cofiberSequenceFunctor_inclusion_differential
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (q : ℤ) :
    ((cofiberSequenceFunctor j).obj F).differential (q, .target) =
      inclusionInteger (j := j) q F := rfl

/-- The cofiber differential is the original boundary and scalar suspension inverse. -/
theorem cofiberSequenceFunctor_connecting_differential
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (q : ℤ) :
    ((cofiberSequenceFunctor j).obj F).differential (q, .cofiber) =
      connecting (j := j) q F := rfl

/-- Every source component is the integer image of the original Arrow left component. -/
theorem cofiberSequenceFunctor_map_source
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (m : F ⟶ G) (q : ℤ) :
    ((cofiberSequenceFunctor j).map m).app (q, .source) =
      (integerPiFunctor j q).map m.left := rfl

/-- Every target component is the integer image of the original Arrow right component. -/
theorem cofiberSequenceFunctor_map_target
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (m : F ⟶ G) (q : ℤ) :
    ((cofiberSequenceFunctor j).map m).app (q, .target) =
      (integerPiFunctor j q).map m.right := rfl

/-- Every cofiber component retains the entire original I-Q cofiber map. -/
theorem cofiberSequenceFunctor_map_cofiber
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (m : F ⟶ G) (q : ℤ) :
    ((cofiberSequenceFunctor j).map m).app (q, .cofiber) =
      (integerPiFunctor j q).map ((cofiber (B := B) (I := I)).map m) := rfl

/-- Every integer differential square is the original full native-square naturality. -/
theorem cofiberSequenceFunctor_naturality
    {F G : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (m : F ⟶ G) (i : Index) :
    ((cofiberSequenceFunctor j).map m).app i ≫
        ((cofiberSequenceFunctor j).obj G).differential i =
      ((cofiberSequenceFunctor j).obj F).differential i ≫
        ((cofiberSequenceFunctor j).map m).app (next i) :=
  ((cofiberSequenceFunctor j).map m).comm i

/-- Every original native position has its literal image equals kernel subgroup equality. -/
theorem cofiberSequenceFunctor_kernel_eq_range
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (i : Index) :
    (((cofiberSequenceFunctor j).obj F).differential (next i)).hom.ker =
      (((cofiberSequenceFunctor j).obj F).differential i).hom.range :=
  ((cofiberSequenceFunctor j).obj F).kernel_eq_range i

end HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerSequence

namespace PointedCGWH.Spectra.NativeStableCofiberIntegerSequence

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerSequence
  (cofiberSequenceFunctor)
open CategoryTheory.Spectra.SpectrumIndexMaps
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Sequential terms retain the original integer functor and the same chosen I-Q cofiber. -/
def sequentialTerm (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) : Index → GrpCat.{v}
  | (q, .source) => (integerStablePiFunctor q).obj F.left
  | (q, .target) => (integerStablePiFunctor q).obj F.right
  | (q, .cofiber) => (integerStablePiFunctor q).obj (CofiberIntegerSequence.cofiber.obj F)

/-- The sequential differential retains the original source, inclusion and scalar connection. -/
def sequentialDifferential (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    ∀ i, sequentialTerm F i ⟶ sequentialTerm F (next i)
  | (q, .source) => (integerStablePiFunctor q).map F.hom
  | (q, .target) => CofiberIntegerSequence.inclusionInteger q F
  | (q, .cofiber) => CofiberConnectingIntegerPiGeometry.connecting q F

/-- The original sequential sequence is a complete object with all integer exactness fields. -/
def sequentialSequence (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    GrpCat.IntegerExactSequence.{v} where
  term := sequentialTerm F
  differential := sequentialDifferential F
  differential_comp i := by
    rcases i with ⟨q, p⟩
    cases p with
    | source =>
      apply GrpCat.hom_ext
      ext x
      exact CofiberConnectingIntegerPiGeometry.source_inclusion_null q F x
    | target =>
      apply GrpCat.hom_ext
      ext x
      exact CofiberConnectingIntegerPiGeometry.inclusion_connecting_null q F x
    | cofiber =>
      apply GrpCat.hom_ext
      ext x
      exact CofiberConnectingIntegerPiGeometry.connecting_source_null q F x
  exact i := by
    rcases i with ⟨q, p⟩
    cases p with
    | source => exact CofiberIntegerExactnessGeometry.source_inclusion_mulExact q F
    | target => exact CofiberIntegerExactnessGeometry.inclusion_connecting_mulExact q F
    | cofiber => exact CofiberIntegerExactnessGeometry.connecting_source_mulExact q F

/-- Both original sequential Arrow components and the complete Q-cofiber map act in every degree. -/
def sequentialMap {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (m : F ⟶ G) :
    sequentialSequence F ⟶ sequentialSequence G where
  app i := match i with
    | (q, .source) => (integerStablePiFunctor q).map m.left
    | (q, .target) => (integerStablePiFunctor q).map m.right
    | (q, .cofiber) => (integerStablePiFunctor q).map (CofiberIntegerSequence.cofiber.map m)
  comm i := by
    rcases i with ⟨q, p⟩
    cases p with
    | source => exact (CofiberConnectingIntegerPiGeometry.sourceIntegerNatTrans q).naturality m
    | target => exact CofiberIntegerSequence.inclusionInteger_naturality q m
    | cofiber => exact CofiberConnectingIntegerPiGeometry.connecting_naturality q m

/-- The complete sequential integer cofiber sequence functor on every raw original arrow. -/
def sequentialCofiberSequenceFunctor :
    Arrow PointedCGWH.SequentialSpectrum.{u, v} ⥤ GrpCat.IntegerExactSequence.{v} where
  obj F := sequentialSequence F
  map m := sequentialMap m
  map_id F := by
    apply GrpCat.IntegerExactSequence.Hom.ext
    rintro ⟨q, p⟩
    cases p <;> simp [sequentialMap, sequentialSequence, sequentialTerm]
  map_comp m n := by
    apply GrpCat.IntegerExactSequence.Hom.ext
    rintro ⟨q, p⟩
    cases p <;> simp [sequentialMap, sequentialSequence, sequentialTerm]

/-- The sequential source differential is the actual original integer map. -/
theorem sequentialCofiberSequenceFunctor_source_differential
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (q : ℤ) :
    (sequentialCofiberSequenceFunctor.obj F).differential (q, .source) =
      (integerStablePiFunctor q).map F.hom := rfl

/-- The sequential inclusion differential is the actual original I-Q inclusion. -/
theorem sequentialCofiberSequenceFunctor_inclusion_differential
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (q : ℤ) :
    (sequentialCofiberSequenceFunctor.obj F).differential (q, .target) =
      CofiberIntegerSequence.inclusionInteger q F := rfl

/-- The sequential cofiber differential keeps the original predecessor degree connection. -/
theorem sequentialCofiberSequenceFunctor_connecting_differential
    (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (q : ℤ) :
    (sequentialCofiberSequenceFunctor.obj F).differential (q, .cofiber) =
      CofiberConnectingIntegerPiGeometry.connecting q F := rfl

/-- Every sequential source map keeps the complete original left Arrow component. -/
theorem sequentialCofiberSequenceFunctor_map_source
    {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (m : F ⟶ G) (q : ℤ) :
    (sequentialCofiberSequenceFunctor.map m).app (q, .source) =
      (integerStablePiFunctor q).map m.left := rfl

/-- Every sequential target map keeps the complete original right Arrow component. -/
theorem sequentialCofiberSequenceFunctor_map_target
    {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (m : F ⟶ G) (q : ℤ) :
    (sequentialCofiberSequenceFunctor.map m).app (q, .target) =
      (integerStablePiFunctor q).map m.right := rfl

/-- Every sequential cofiber map keeps the full original I-Q pushout map. -/
theorem sequentialCofiberSequenceFunctor_map_cofiber
    {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (m : F ⟶ G) (q : ℤ) :
    (sequentialCofiberSequenceFunctor.map m).app (q, .cofiber) =
      (integerStablePiFunctor q).map (CofiberIntegerSequence.cofiber.map m) := rfl

/-- The complete symmetric sequence uses the original
sequential-to-symmetric enriched restriction. -/
def symmetricCofiberSequenceFunctor :
    Arrow SymmetricCarrier.{u, v} ⥤ GrpCat.IntegerExactSequence.{v} :=
  cofiberSequenceFunctor sequentialSymmetricOperatorIndexFunctor.{u, v}

/-- The complete orthogonal sequence uses the original composite
enriched index restriction. -/
def orthogonalCofiberSequenceFunctor :
    Arrow OrthogonalCarrier.{u, v} ⥤ GrpCat.IntegerExactSequence.{v} :=
  cofiberSequenceFunctor sequentialOrthogonalOperatorIndexFunctor.{u, v}

end PointedCGWH.Spectra.NativeStableCofiberIntegerSequence

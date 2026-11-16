/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
public import Batteries.Util.ProofWanted

/-!
# Wanted full source coefficient-image realization

Generic coefficient diagrams, augmented-module localization and raw
geometric realization are explicit construction requests. The compatible
QCoh factory chooses its enhancement, whole coefficient diagram, unit
augmentation and full geometric comparison together. No adapter is
promised for an arbitrary independently chosen objectwise source model.

References: Keller, Deriving DG categories, §§1/6; HAG II
math/0404373v7 §1.3.7; Lurie HTT §§2.2 and 3.3.3.
-/

open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
open MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels

universe u
variable (k : Type u) [CommRing k] (L : CochainLiftModel k)
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (X : Prestack k) (C : FamilyCoefficientCategory L N X) (R : RawModuleRealization M)

def_wanted native_coefficient_section_diagrams : SectionDiagrams C

def_wanted native_geometric_coefficient_closed_functor (B : SectionDiagrams C) :
    GeometricClosedFunctor C R B

def_wanted augmented_coefficient_categorical_localization (B : SectionDiagrams C)
    (F : GeometricClosedFunctor C R B) : GeometricCoefficientLocalization C R B F

def_wanted whole_raw_coefficient_geometric_realization (B : SectionDiagrams C) :
    RawGeometricRealization C R B

def_wanted localized_coefficient_geometric_realization (B : SectionDiagrams C)
    (F : GeometricClosedFunctor C R B) (P : GeometricCoefficientLocalization C R B F)
    (T : RawGeometricRealization C R B) : GeometricCoefficientRealization C R B F P T

def_wanted native_source_coefficient_image_inclusion (B : SectionDiagrams C)
    (G : QCohEnhancement M U X) (D : CoefficientDiagramSystem C G)
    (V : UnitCoefficientDiagram C G D) (P : SourceEnrichedQCohModel C G R D V) :
    ImageInclusion C R B G D

def_wanted source_compatible_coefficient_image_qcoh :
    Σ G : QCohEnhancement M U X, Σ D : CoefficientDiagramSystem C G,
      Σ V : UnitCoefficientDiagram C G D, SourcedCoefficientImageModel C R G D V

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.OrdinaryFamilyCoefficientModels

/-!
# Native all-affine ordinary coefficient and perfect-category construction

Actual rings, all affine-family arrows, full DG generators, source
augmentations and comparisons of whole functors are fixed first.
These are genuine construction and proof requests; arc descent is
not an input to any source construction.

Sources: Keller Sections1/2/6; HAGII math/0404373v7 Section1.3.7;
Bhatt--Mathew1807.04725v4 Section5.4.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.OrdinaryFamilyCoefficientModels

open MathlibExt.AlgebraicGeometry.GeneralArcCoverModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels

variable (L : CochainLiftModel ℤ) (N : ShuffleAlgebraFunctor ℤ) (X : QcqsScheme)

def_wanted ordinary_family_coefficient_category : FamilyCoefficientCategory L N X

variable {L N X} (C : FamilyCoefficientCategory L N X)
  {S : AffineScalarSystem N} (M : AffineModuleFibration N S) (R : RawModuleRealization M)

def_wanted ordinary_coefficient_section_diagrams : SectionDiagrams C

variable (B : SectionDiagrams C)

def_wanted ordinary_geometric_closed_functor : GeometricClosedFunctor C M R B

def_wanted ordinary_coefficient_localization (F : GeometricClosedFunctor C M R B) :
  CoefficientLocalization C M R B F

def_wanted ordinary_raw_coefficient_realization : RawRealization C M R B

def_wanted ordinary_full_qcoh_realization (F : GeometricClosedFunctor C M R B)
    (P : CoefficientLocalization C M R B F) (T : RawRealization C M R B) :
  QCohRealization C M R B F P T

variable {F : GeometricClosedFunctor C M R B} {P : CoefficientLocalization C M R B F}
  {T : RawRealization C M R B} (K : QCohRealization C M R B F P T)

def_wanted ordinary_perfect_comparison : PerfectComparison C M R B K

theorem_wanted ordinary_perfect_comparison_weak (I : PerfectComparison C M R B K) :
  CategoricalWeakEquivalence I.map

end MathlibExt.AlgebraicGeometry.OrdinaryFamilyCoefficientModels

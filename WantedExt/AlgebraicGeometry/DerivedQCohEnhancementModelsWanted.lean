/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
public import Batteries.Util.ProofWanted

/-!
# Native coefficient/QCoh enhancement construction requests

Every output has the complete source object, scalar, Hom and native
coherent-nerve normalization recorded in its public contract. A scalar
adapter is requested together with the compatible global enhancement;
categorical weak equivalence alone does not imply k-linear realization.

References: Toën--Vezzosi HAG II, Part 2; Lurie Higher Algebra §7.3;
PTVV arXiv:1111.3209v4, §2.1. Generic coherent assembly remains open.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels

open _root_.CategoryTheory
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies

universe u

def_wanted normalizedCochainLift (k : Type u) [CommRing k] : CochainLiftModel k

def_wanted naturalCoefficientNerveLift (k : Type u) [CommRing k]
    (L : CochainLiftModel k) : NerveLiftModel L

def_wanted regularUnitSection (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) : RegularUnitSystem M

def_wanted fullQCohModel (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (X : Prestack k) : QCohEnhancement M U X

def_wanted affineQCohUnitModel (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (A : SAlg k) : AffineQCohNormalization M U Q A

def_wanted normalizedCoefficientQCohModel (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (A : SAlg k) (B : AffineQCohNormalization M U Q A)
    (X : Prestack k) (b : X ⟶ affineMapping k Q A) :
    CoefficientQCohEnhancement M U Q L V A B X b

end MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels

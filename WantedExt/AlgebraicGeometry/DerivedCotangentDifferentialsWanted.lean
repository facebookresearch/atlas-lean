/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
public import MathlibExt.AlgebraicGeometry.DerivedStableQCohModels
public import MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
public import Batteries.Util.ProofWanted

/-!
# Wanted native global cotangent differentials

Generic slice maps, stable DG pullbacks and the entire cotangent
Yoneda transpose are construction requests. The differential uses
the actual X(E) → Y(E) based map, with a normalized homotopy in the
relative mapping space over every coefficient test. The stable
pullback factory chooses compatible enhancements together.

The differential is the transpose relative to a chosen along
representation, hence determined only up to the automorphisms of the
pulled-back cotangent; the canonical representation (restriction of the
target's universal derivation along f), with the chain rule and
d(id) = id, is not requested here.

References: HAG II math/0404373v7 §1.4.1; PTVV1111.3209v4 §2.2.
-/

open _root_.CategoryTheory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedAlongDerivations
open MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
open MathlibExt.AlgebraicGeometry.DerivedStableQCohModels

universe u

def_wanted native_initial_slice_precomposition (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (X : Prestack k) (G : QCohEnhancement M U X) (V W : G.category)
    (d : DGHom (LargeScalar k) 0 V W) (hd : d ∈ dgCycles (LargeScalar k) V W) :
    SlicePrecomposition d hd

def_wanted source_compatible_dg_qcoh_pullbacks (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (X Y : Prestack k) (f : X ⟶ Y) :
    Σ GY : QCohEnhancement M U Y, Σ GX : QCohEnhancement M U X,
      StableQCohModel GY × StableQCohModel GX × PullbackDGModel f GY GX

def_wanted coherent_cotangent_context (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (X : DerivedStack Q) (geometric : IsDerivedArtin X)
    (lfp : IsLocallyOfFinitePresentationStack X) [SSet.Quasicategory (qcoh M X.functor)]
    (G : QCohEnhancement M U X.functor) (stable : StableQCohModel G) : CotangentContext R G

def_wanted pulled_cotangent_along_representation (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (X Y : DerivedStack Q) (GX : QCohEnhancement M U X.functor)
    (GY : QCohEnhancement M U Y.functor)
    (stableX : StableQCohModel GX) (stableY : StableQCohModel GY)
    (CX : CotangentContext R GX) (CY : CotangentContext R GY)
    (f : StackMap X Y) (PB : PullbackDGModel f GY GX)
    (A : AlongLiftProjection M R CX.kernels f CX.projection)
    (B : AlongPath M R CX.kernels Y.functor)
    (D : AlongDerivationModel M R CX.kernels f CX.projection A B)
    (DF : AlongFibration M R CX.kernels D) :
    AlongCotangentRepresentation CX f A B D DF (PB.functor.obj CY.cotangent.object)

def_wanted native_global_cotangent_differential (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (X Y : DerivedStack Q) (GX : QCohEnhancement M U X.functor)
    (GY : QCohEnhancement M U Y.functor)
    (stableX : StableQCohModel GX) (stableY : StableQCohModel GY)
    (CX : CotangentContext R GX) (CY : CotangentContext R GY)
    (f : StackMap X Y) (PB : PullbackDGModel f GY GX)
    (A : AlongLiftProjection M R CX.kernels f CX.projection)
    (B : AlongPath M R CX.kernels Y.functor) (T : AlongPathMap M R CX.kernels f CX.path B)
    (a : AlongRawMap M R CX.kernels f CX.projection A CX.path B T)
    (D : AlongDerivationModel M R CX.kernels f CX.projection A B)
    (r : AlongReplacementMap M R CX.kernels a CX.derivations D)
    (DF : AlongFibration M R CX.kernels D)
    (m : AlongFibrationMap M R CX.kernels r CX.fibration DF)
    (C : AlongCotangentRepresentation CX f A B D DF (PB.functor.obj CY.cotangent.object)) :
    CotangentDifferential CX CY f PB r DF m C

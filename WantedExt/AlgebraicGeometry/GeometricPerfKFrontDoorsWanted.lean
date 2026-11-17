/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeometricPerfKFrontDoors

/-!
# Native geometric Perf presentations and canonical support/quotient maps

All underlying module categories, original pullbacks, support predicates,
full inclusions and whole-functor normalization maps are fixed first.
K remains the native S-construction. Genuine presentation, stability and
exactness constructions are separate Wanted work.

Sources: Thomason--Trobaugh localization; BGT1001.2282v4 Sections4/5/7.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.GeometricPerfKFrontDoors

open _root_.CategoryTheory _root_.AlgebraicGeometry
open GeneralArcCoverModels OrdinarySchemeModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.BGTVerdierQuotients

def_wanted ordinary_geometric_perfect_input {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : QcqsScheme) : PerfectInput (OrdinarySchemeModuleFamilies.perf M X)

def_wanted ordinary_geometric_perfect_pullback {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) {X Y : QcqsScheme} (f : X ⟶ Y)
    (I : PerfectInput (OrdinarySchemeModuleFamilies.perf M Y))
    (J : PerfectInput (OrdinarySchemeModuleFamilies.perf M X)) :
  PerfectMap I J (OrdinarySchemeModuleFamilies.perfPullback M f)

def_wanted derived_stack_large_perfect_source {k : Type} [CommRing k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} (M : AffineModuleFibration N S)
    (X : Prestack k) : LargePerfectSource (DerivedQCohModuleFamilies.perf M X)

def_wanted derived_stack_perfect_pullback {k : Type} [CommRing k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} (M : AffineModuleFibration N S)
    {X Y : Prestack k} (f : X ⟶ Y)
    (I : PerfectInput (DerivedQCohModuleFamilies.perf M Y))
    (J : PerfectInput (DerivedQCohModuleFamilies.perf M X)) :
  PerfectMap I J (DerivedQCohModuleFamilies.perfPullback M f)

def_wanted ordinary_supported_perfect_input {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) {X U : QcqsScheme} (j : U ⟶ X) [IsOpenImmersion j]
    (I : PerfectInput (OrdinarySchemeModuleFamilies.perf M X))
    (J : PerfectInput (OrdinarySchemeModuleFamilies.perf M U)) :
  SupportedInput I J (OrdinarySchemeModuleFamilies.perfPullback M j)

def_wanted native_support_verdier_quotient {X Y : SSet.{1}} {I : PerfectInput X} {U : PerfectInput Y}
    {r : X ⟶ Y} (P : SupportedInput I U r) : StableVerdierQuotient (supportedStableInclusion P)

def_wanted native_quotient_restriction {X Y : SSet.{1}} {I : PerfectInput X} {U : PerfectInput Y}
    {r : X ⟶ Y} (P : SupportedInput I U r) (F : PerfectMap I U r)
    (Q : StableVerdierQuotient (supportedStableInclusion P)) : QuotientRestriction P F Q

def_wanted native_ring_perfect_input (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ) : RingPerfectInput A N

end MathlibExt.AlgebraicGeometry.GeometricPerfKFrontDoors

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.OrdinarySchemeModuleFamilies
public import MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels
public import MathlibExt.AlgebraicGeometry.EnhancedPerfKModels
public import MathlibExt.AlgebraicTopology.NativeK0ComparisonModels
public import MathlibExt.AlgebraicTopology.BGTVerdierQuotients

/-!
# Actual geometric Perf inputs, supported objects and canonical K maps

Large inputs are the whole native ordinary-scheme or derived-prestack
Perf categories. A genuine small perfect presentation preserves that
entire category, and exact maps carry a comparison of whole functors.
K is the already fixed native S-construction on the small presentation.

Supported objects are the full native subcategory annihilated by the
actual open restriction. The quotient is the original full stable
Verdier construction; its canonical map to the open Perf is normalized
by the whole restriction functor. It is not declared an equivalence
before idempotent completion.

Sources: Thomason--Trobaugh, Higher algebraic K-theory of schemes and
derived categories, localization; BGT1001.2282v4 Sections4/5/7/9.
Native module, finite-cell, full DG, spectrum and quotient source pins
and license notices are retained in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricPerfKFrontDoors

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open GeneralArcCoverModels OrdinarySchemeModuleFamilies OrdinaryConstantCoefficientModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
open MathlibExt.AlgebraicTopology.StableInfinityMappingSpaces
open MathlibExt.AlgebraicTopology.StableInfinityMappingSpaceMaps
open MathlibExt.AlgebraicTopology.StableInfinityKSpectra
open MathlibExt.AlgebraicTopology.BGTVerdierQuotients
open MathlibExt.AlgebraicTopology.NativeK0ComparisonModels
open MathlibExt.AlgebraicTopology.StableSpectraInfinitySource
open MathlibExt.AlgebraicTopology.NativeSpectrumConeSources
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The full geometric category and its genuine small idempotent-complete presentation. -/
structure PerfectInput (X : SSet.{1}) where
  large : PerfectInfinityCategory.{1}
  normalized : large.toStableInfinityCategory.toSSet = X
  small : PerfectInfinityCategory.{0}
  comparison : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj small.toStableInfinityCategory.toSSet ⟶ X
  weak : CategoricalWeakEquivalence comparison

/-- Essential smallness is recorded by an actual whole-category presentation, independently of K. -/
structure SmallPerfectSource (X : SSet.{1}) where
  small : PerfectInfinityCategory.{0}
  comparison : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj small.toStableInfinityCategory.toSSet ⟶ X
  weak : CategoricalWeakEquivalence comparison

/-- The whole large native category has its genuine stable/idempotent-complete structure. -/
structure LargePerfectSource (X : SSet.{1}) where
  large : PerfectInfinityCategory.{1}
  normalized : large.toStableInfinityCategory.toSSet = X

/-- This combines the two independently recorded native sources without changing their maps. -/
def perfectInputOfSources {X : SSet.{1}} (L : LargePerfectSource X) (P : SmallPerfectSource X) : PerfectInput X where
  large := L.large
  normalized := L.normalized
  small := P.small
  comparison := P.comparison
  weak := P.weak

/-- A canonical exact map retains the entire original geometric functor. -/
structure PerfectMap {X Y : SSet.{1}} (I : PerfectInput X) (J : PerfectInput Y) (f : X ⟶ Y) where
  small : ExactFunctor I.small.toStableInfinityCategory J.small.toStableInfinityCategory
  whole_normalization : NaturallyEquivalentMaps
    ((SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).map small.map ≫ J.comparison) (I.comparison ≫ f)

/-- The actual geometric connective K entry uses the original native S spectrum. -/
def geometricK (K : ConnectiveKConstruction) {X : SSet.{1}} (I : PerfectInput X) : SymmetricSpectrum :=
  connectiveK K I.small.toStableInfinityCategory

/-- Its map is the original source-normalized K map of that same exact functor. -/
def geometricKMap (K : ConnectiveKConstruction) {X Y : SSet.{1}} {I : PerfectInput X} {J : PerfectInput Y}
    {f : X ⟶ Y} (F : PerfectMap I J f) : geometricK K I ⟶ geometricK K J := connectiveKMap K F.small

/-- The literal native stable sphere-Hom group supplies the geometric K0 entry. -/
def geometricK0 {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S} (G : SpectrumGroupSource S Z)
    (K : ConnectiveKConstruction) {X : SSet.{1}} (I : PerfectInput X) : Type 1 := spectrumPi0 G (geometricK K I)

/-- Support is vanishing under the actual original restriction, with every coherent arrow retained. -/
def supportedPerf {X Y : SSet.{1}} (U : PerfectInput Y) (restriction : X ⟶ Y) : SSet.{1} :=
  (X.fullEnhancedSubcategory (fun x : X _⦋0⦌ =>
    IsZeroObject U.large.toStableInfinityCategory.toSSet
      ((restriction ≫ eqToHom U.normalized.symm).app (op ⦋0⦌) x))).toSSet

/-- The native support inclusion is the original full subcomplex map. -/
def supportInclusion {X Y : SSet.{1}} (U : PerfectInput Y) (restriction : X ⟶ Y) : supportedPerf U restriction ⟶ X :=
  (X.fullEnhancedSubcategory (fun x : X _⦋0⦌ =>
    IsZeroObject U.large.toStableInfinityCategory.toSSet
      ((restriction ≫ eqToHom U.normalized.symm).app (op ⦋0⦌) x))).ι

/-- Fullness is requested for that same canonical source inclusion. -/
structure SupportedInput {X Y : SSet.{1}} (I : PerfectInput X) (U : PerfectInput Y) (restriction : X ⟶ Y) where
  input : PerfectInput (supportedPerf U restriction)
  inclusion : PerfectMap input I (supportInclusion U restriction)
  full : IsFullyFaithful inclusion.small.map

def supportedStableInclusion {X Y : SSet.{1}} {I : PerfectInput X} {U : PerfectInput Y}
    {restriction : X ⟶ Y} (P : SupportedInput I U restriction) :
    FullStableInclusion P.input.small.toStableInfinityCategory I.small.toStableInfinityCategory :=
  ⟨P.inclusion.small, P.full⟩

/-- The actual raw Verdier quotient maps to the open category by the entire original restriction. -/
structure QuotientRestriction {X Y : SSet.{1}} {I : PerfectInput X} {U : PerfectInput Y}
    {restriction : X ⟶ Y} (P : SupportedInput I U restriction) (F : PerfectMap I U restriction)
    (Q : StableVerdierQuotient (supportedStableInclusion P)) where
  functor : ExactFunctor Q.category U.small.toStableInfinityCategory
  whole_normalization : NaturallyEquivalentMaps (Q.quotient.map ≫ functor.map) F.small.map

/-- An ordinary ring's native finite-cell/retract perfect DG category is the actual source. -/
structure RingPerfectInput (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ) where
  model : MathlibExt.CategoryTheory.PerfectDGModuleModels.SmallPerfectModel (ringCategory A N)
  input : EnhancedPerfKModels.EnhancedPerfectInput model

def ringK (K : ConnectiveKConstruction) {A : OrdinaryAlgebras} {N : ShuffleAlgebraFunctor ℤ}
    (I : RingPerfectInput A N) : SymmetricSpectrum := connectiveK K I.input.category.toStableInfinityCategory

end MathlibExt.AlgebraicGeometry.GeometricPerfKFrontDoors

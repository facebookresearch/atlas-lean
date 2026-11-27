/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.BGTNativeNonconnectiveModels

/-!
# Native BGT boundary and nonconnective source requests

The actual Ind/compact/Verdier sources, K parameter homotopy, native loop
maps and whole ordinal diagram are fixed before the colimit request.
The stage constructor produces the swindle contraction as an output;
it does not receive K vanishing or a motive equivalence as a hypothesis.

Source: BGT1001.2282v4, Definitions 9.1 and 9.6, Lemma 9.4.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.BGTNativeNonconnectiveModels

open _root_.CategoryTheory
open StableInfinityCategoryModels StableInfinityFilteredColimits
open NativeKParametrizedSource NativeSpectraSimplicialSource
open NativeEnrichedSpectrumReplacements StableSpectraInfinitySource NativeSpectrumConeSources
open BGTVerdierQuotients
open MathlibExt.SpectraSource

/-- Construct the original source Sigma objects and native exact maps on all small stable categories. -/
def_wanted native_sigma_kappa_system (k : UncountableRegularCardinal) : SigmaKappaSystem k

/-- Construct the canonical source quotient homotopies, swindle contractions and actual native
boundaries on all small stable categories, naturally in the category (BGT, Def. 9.6 and the
natural sequence before Lemma 9.4). -/
def_wanted native_k_boundary_stages {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} (Z : SpectrumZeroSource S)
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) :
    {B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C //
      IsNaturalBoundary Z K R L P B}

/-- Construct the actual native derived colimit on the already fixed whole sequence. -/
def_wanted native_spectrum_sequential_colimit (S : SpectrumInfinitySource) (D : ℕ ⥤ SymmetricSpectrum) :
  SpectrumSequentialColimit S D

/-- Extend the original whole sequence arrow to the actual universal coherent colimit cocones. -/
def_wanted native_spectrum_colimit_map {S : SpectrumInfinitySource} {D E : ℕ ⥤ SymmetricSpectrum}
    (a : StableSequenceMap S D E) (C : SpectrumSequentialColimit S D)
    (F : SpectrumSequentialColimit S E) : SpectrumColimitMap a C F

/-- The original exact functor induces the whole canonical source sequence map on every native term,
for natural boundary stages. -/
def_wanted native_nonconnective_tower_map {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C)
    (hB : IsNaturalBoundary Z K R L P B)
    {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D) : SourceTowerMap K R L P B f

/-- BGT9.34 produces the actual native cofiber square for the original two nonconnective exact maps. -/
def_wanted native_nonconnective_localization {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} (Z : SpectrumZeroSource S)
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C)
    (E : StableExactSequence.{0})
    (a : SourceTowerMap K R L P B E.inclusion.functor)
    (b : SourceTowerMap K R L P B E.quotientMap)
    (C_A : SpectrumSequentialColimit S (nonconnectiveTower K R L P B E.left))
    (C_B : SpectrumSequentialColimit S (nonconnectiveTower K R L P B E.middle))
    (C_C : SpectrumSequentialColimit S (nonconnectiveTower K R L P B E.right))
    (m_a : SpectrumColimitMap a.toStableSequenceMap C_A C_B)
    (m_b : SpectrumColimitMap b.toStableSequenceMap C_B C_C) :
    NonconnectiveExactSquare Z a.toStableSequenceMap b.toStableSequenceMap C_A C_B C_C m_a m_b

end MathlibExt.AlgebraicTopology.BGTNativeNonconnectiveModels

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeMotiveGenerators

/-!
# Native motive generator, reduction and localization construction requests

These choose actual full source functors, cofibers and canonical comparison
maps. No K/motive equivalence is required by any constructor.
Sources: BGT arXiv:1001.2282v4 Sections 5--6/8.1--8.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeMotiveGenerators

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.SpectraSource
open NativeKParametrizedSource NativeMotivePresheafSources NativeMotiveLocalizationModels
open StableSpectraInfinitySource StableInfinityFilteredColimits
open scoped Cardinal


def_wanted native_motive_presheaf_setup {A : StableCategoryEnrichment} {k : Cardinal.{0}}
    (T : SpectralCompactSource A k) (S : SpectrumInfinitySource) : MotivePresheafSetup T S

def_wanted native_source_exact_square (A : StableCategoryEnrichment) (Z : ZeroCategorySource)
    (E : PerfectExactSequence) : SourceExactSquare A Z E

variable {A : StableCategoryEnrichment} {k : Cardinal.{0}} {T : SpectralCompactSource A k}
  {S : SpectrumInfinitySource} (V : MotivePresheafSetup T S)

def_wanted native_reduced_spectral_yoneda : ReducedYonedaSource V

def_wanted native_localizing_generator_family (D : ReducedYonedaSource V) : LocalizingGeneratorFamily D

def_wanted native_filtered_motive_comparisons (D : ReducedYonedaSource V) : FilteredComparisonFamily D

def_wanted native_additive_generator_presentation {T : SpectralCompactSource A ℵ₀}
    (V : MotivePresheafSetup T S) (D : ReducedYonedaSource V) :
    letI := T.enrichment; letI := V.colimits
    SmallGeneratorPresentation V.presheaves V.ends V.replacements (additiveGenerators D)

def_wanted native_localizing_generator_presentation {k : UncountableRegularCardinal}
    {T : SpectralCompactSource A k.value} (V : MotivePresheafSetup T S) (D : ReducedYonedaSource V)
    (L : LocalizingGeneratorFamily D) (F : FilteredComparisonFamily D) :
    letI := T.enrichment; letI := V.colimits
    SmallGeneratorPresentation V.presheaves V.ends V.replacements (localizingGenerators D L F)

def_wanted native_additive_motive {T : SpectralCompactSource A ℵ₀} (V : MotivePresheafSetup T S)
    (D : ReducedYonedaSource V) : additiveMotive V D

def_wanted native_localizing_motive {k : UncountableRegularCardinal} {T : SpectralCompactSource A k.value}
    (V : MotivePresheafSetup T S) (D : ReducedYonedaSource V)
    (L : LocalizingGeneratorFamily D) (F : FilteredComparisonFamily D) : localizingMotive V D L F

end MathlibExt.AlgebraicTopology.NativeMotiveGenerators

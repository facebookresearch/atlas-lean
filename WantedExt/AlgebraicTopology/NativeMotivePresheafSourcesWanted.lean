/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeMotivePresheafSources

/-!
# Construction and action-relation proofs for the actual complete presheaf source

Every carrier and map is the native one in MathlibExt. These source
requests contain no additive/localizing equivalence or K corepresentability
assumption. Source: BGT arXiv:1001.2282v4 Sections 6--9; HSS Sections 2--3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeMotivePresheafSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.SpectraSource
open NativeKParametrizedSource StableSpectraInfinitySource NativeSpectralPresheafModels

variable (C : Type) [EnrichedCategory SymmetricSpectrum C]

theorem_wanted native_end_precomposition {E F : RawPresheaf C} (f : E ⟶ F) (G : RawPresheaf C) :
  PrecompositionCompatible C f G

theorem_wanted native_end_postcomposition (E : RawPresheaf C) {F G : RawPresheaf C} (g : F ⟶ G) :
  PostcompositionCompatible C E g

theorem_wanted native_end_functoriality : EndFunctoriality C

def_wanted native_suspension_plus_source : SuspensionPlusSource

def_wanted native_presheaf_simplicial_enrichment : PresheafSimplicialEnrichment C

def_wanted native_presheaf_coherent_source (S : SpectrumInfinitySource)
    (H : PresheafSimplicialEnrichment C) (P : NativeSpectralPresheafModels.PresheafInfinitySource C S) :
    PresheafCoherentSource C S H P

variable {A : StableCategoryEnrichment} {k : Cardinal.{0}} (T : SpectralCompactSource A k)

def_wanted native_restricted_spectral_yoneda
    (H : letI := T.enrichment; PresheafSimplicialEnrichment T.index) :
    RestrictedYonedaSource T H

def_wanted native_restricted_spectral_representable
    (H : letI := T.enrichment; PresheafSimplicialEnrichment T.index)
    (Y : RestrictedYonedaSource T H) (c : T.index) : RestrictedRepresentable Y c

end MathlibExt.AlgebraicTopology.NativeMotivePresheafSources

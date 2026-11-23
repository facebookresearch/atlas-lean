/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeIKFunctorSources

/-!
# Full source functoriality and invariant proofs for the original native IK tower

No spectra or maps are defined by motive equivalences. The entire native
tower, all term parameter maps and augmented colimit functor are fixed.
Source: BGT arXiv:1001.2282v4 Sections 9.1--9.2; HSS Sections 2--3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeIKFunctorSources

open NativeKParametrizedSource NativeSpectraSimplicialSource StableSpectraInfinitySource
open NativeEnrichedSpectrumReplacements NativeSpectrumConeSources NativeDerivedSpectrumModels
open BGTNativeNonconnectiveModels StableInfinityCategoryModels StableInfinityFilteredColimits

/-- Construct the Sigma objects and maps together with their strict enriched action. For an
arbitrary Sigma system the action need not exist: equivalent but non-isomorphic quotient models
chosen for isomorphic categories cannot be strictly functorial. -/
def_wanted native_sigma_full_parameters (A : StableCategoryEnrichment)
    (k : UncountableRegularCardinal) : Σ P : SigmaKappaSystem k, SigmaFunctorAction A P

def_wanted native_closed_loop_parameters (N : SpectrumSimplicialEnrichment) {S : SpectrumInfinitySource}
    (R : EnrichedSpectrumReplacements N S) : LoopFunctorActions N R

variable {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal} (P : SigmaKappaSystem k)
    (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C)

/-- The IK tower functor, for a Sigma system with a strict enriched action and natural boundary
stages. -/
def_wanted native_full_IK_tower_functor (sig : SigmaFunctorAction A P)
    (hB : IsNaturalBoundary Z K R L P B) : NativeIKSource K R L P B

def_wanted native_IK_localizing_invariant (I : NativeIKSource K R L P B) : NativeIKLocalizing I

end MathlibExt.AlgebraicTopology.NativeIKFunctorSources

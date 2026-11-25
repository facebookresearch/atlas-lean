/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeKCorepresentabilityModels

/-!
# Native K presheaf, canonical mapping-spectrum and BGT equivalence requests

Construction, reflection and point-set rectification are separated from
the final equivalence. Rectification uses an actual cofibrant source and
fibrant target. BGT7.13 is explicitly scoped to perfect A and the omega
compact source; arbitrary raw A requires its actual Idem completion.
Sources: BGT arXiv:1001.2282v4 Section 7.3, especially Theorem 7.13;
HSS Sections 3.1--3.4. No K spectrum is defined by this theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeKCorepresentabilityModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.SpectraSource
open StableInfinityCategoryModels NativeKParametrizedSource NativeSpectraSimplicialSource
open NativeMotivePresheafSources NativeMotiveGenerators NativeMotiveLocalizationModels
open NativeSpectralPresheafModels StableSpectraInfinitySource NativeDerivedSpectrumModels
open scoped Cardinal

def_wanted native_full_stable_exact_functor_input (B A : StableInfinityCategory.{0}) :
    FullStableExactFunctorInput B A

def_wanted native_core_to_zero_fold (C : StableInfinityCategory.{0}) : CoreToZeroFold C

variable {A : StableCategoryEnrichment} {k : Cardinal.{0}} {T : SpectralCompactSource A k}
    {S : SpectrumInfinitySource} (V : MotivePresheafSetup T S) {D : StableInfinityCategory.{0}}
    {N : SpectrumSimplicialEnrichment} (K : ParametrizedKSource A N)

def_wanted native_full_exact_presheaf_input : FullExactPresheafInput (T := T) D

variable (J : FullExactPresheafInput (T := T) D)

def_wanted native_full_K_presheaf : KPresheafSource K J

variable (E : KPresheafSource K J)

def_wanted native_raw_yoneda_to_K : RawYonedaToKSource V K J E

def_wanted native_reduced_yoneda_to_K (U : ReducedYonedaSource V) (F : RawYonedaToKSource V K J E) :
    ReducedKFactor U F

theorem_wanted native_K_presheaf_additive_local (U : ReducedYonedaSource V) :
    letI := T.enrichment; letI := V.colimits
    IsLocalVertex V.presheaves V.ends V.replacements (additiveGenerators U)
      (presheafVertex V.presheaves (V.replacements.fibrant.obj E.presheaf))

theorem_wanted native_restricted_yoneda_cofibrant (c : T.index) :
    letI := T.enrichment; letI := V.colimits
    IsProjectivelyCofibrant T.index (V.rawYoneda (T.represented c))

theorem_wanted native_restricted_yoneda_end_augmentation (c : T.index)
    (F : letI := T.enrichment; RawPresheaf T.index)
    (fibrant : letI := T.enrichment; ∀ d : T.index, IsOmegaFibrant (value T.index F d)) :
    letI := T.enrichment; letI := V.colimits
    IsStableWeak S (endCofibrantAugmentation V c F)

def_wanted native_reflected_K_factor (U : ReducedYonedaSource V) (F : RawYonedaToKSource V K J E)
    (B : ReducedKFactor U F) (G : letI := T.enrichment; Set (RawMotiveGenerator (C := T.index)))
    (M : letI := T.enrichment; letI := V.colimits;
      MotiveLocalization V.presheaves V.ends V.replacements G)
    (localObject : letI := T.enrichment; letI := V.colimits;
      IsLocalVertex V.presheaves V.ends V.replacements G
        (presheafVertex V.presheaves (V.replacements.fibrant.obj E.presheaf))) :
    ReflectedKFactor U F B G M

def_wanted native_K_mapping_rectification (U : ReducedYonedaSource V) (F : RawYonedaToKSource V K J E)
    (B : ReducedKFactor U F) (G : letI := T.enrichment; Set (RawMotiveGenerator (C := T.index)))
    (M : letI := T.enrichment; letI := V.colimits;
      MotiveLocalization V.presheaves V.ends V.replacements G)
    (L : ReflectedKFactor U F B G M) (c : T.index) (Y : RestrictedRepresentable V.yoneda c)
    (h : letI := T.enrichment; letI := V.colimits;
      IsStableWeak S (endCofibrantAugmentation V c
        (V.replacements.fibrant.obj (V.replacements.fibrant.obj E.presheaf))))
    (Q : SpectrumReplacements S) : KComparisonRectification U F B G M L c Y h Q

/-- The cardinal and idempotence guards are source hypotheses; stable equivalence is the conclusion. -/
theorem_wanted native_additive_corepresentability (omega : k = ℵ₀) (perfect : IsIdempotentComplete D)
    (U : ReducedYonedaSource V) (F : RawYonedaToKSource V K J E) (B : ReducedKFactor U F)
    (M : letI := T.enrichment; letI := V.colimits;
      MotiveLocalization V.presheaves V.ends V.replacements (additiveGenerators U))
    (L : ReflectedKFactor U F B (additiveGenerators U) M)
    (c : T.index) (Y : RestrictedRepresentable V.yoneda c)
    (h : letI := T.enrichment; letI := V.colimits;
      IsStableWeak S (endCofibrantAugmentation V c
        (V.replacements.fibrant.obj (V.replacements.fibrant.obj E.presheaf))))
    (Q : SpectrumReplacements S)
    (C : KComparisonRectification U F B (additiveGenerators U) M L c Y h Q) :
    IsStableWeak S C.map

end MathlibExt.AlgebraicTopology.NativeKCorepresentabilityModels

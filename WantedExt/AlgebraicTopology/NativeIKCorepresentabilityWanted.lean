/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeIKCorepresentabilityModels

/-!
# Source unit, universal localizing extension and BGT9.8 comparison requests

IK is the original native tower. The universal-invariant extension and
native point-set value comparisons are outputs. The canonical mapping
spectrum comparison is already fixed by full native evaluation, the
same spectral-linearity triangle, source sphere K class and tower cocone.
Its stable equivalence is a separate conclusion.
Sources: BGT arXiv:1001.2282v4 Sections 8.3/9.2, Theorems 8.7/9.8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeIKCorepresentabilityModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.SpectraSource
open NativeKParametrizedSource NativeCompactSourceModels NativeMotivePresheafSources
open NativeMotiveGenerators NativeMotiveLocalizationModels NativeMotiveTensorModels
open NativeSpectrumHoClosedModels NativeIKFunctorSources BGTNativeNonconnectiveModels
open NativeSpectraSimplicialSource NativeEnrichedSpectrumReplacements NativeSpectrumConeSources
open StableInfinityCategoryModels StableInfinityFilteredColimits NativeDerivedSpectrumModels StableSpectraInfinitySource


def_wanted native_compact_sphere_index {A : StableCategoryEnrichment} {k : Cardinal.{0}}
    (T : SpectralCompactSource A k) (S : SpectrumInfinitySource) (P : CompactSpectraSource S)
    (compact : IsCompactPerfectCategory A k P.small) : {W : SphereIndexSource T S // W.source = P}

variable {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment} {S : SpectrumInfinitySource}
    {Z : SpectrumZeroSource S} {ki : UncountableRegularCardinal}
    {K : ParametrizedKSource A N} {R : EnrichedSpectrumReplacements N S}
    {L : SpectrumCoherentLocalization N S} {P : SigmaKappaSystem ki}
    {B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C}
    (I : NativeIKSource K R L P B)
    {km : UncountableRegularCardinal} {T : SpectralCompactSource A km.value}
    (V : MotivePresheafSetup T S) (U : ReducedYonedaSource V)
    {Q : LocalizingGeneratorFamily U} {F : FilteredComparisonFamily U}
    (M : localizingMotive V U Q F)

def_wanted native_IK_invariant_extension (localizing : NativeIKLocalizing I) : IKInvariantExtension I V U M

def_wanted native_invariant_object_comparison (H : IKInvariantExtension I V U M)
    (C : PerfectInfinityCategory.{0}) : InvariantObjectComparison H C

def_wanted native_IK_stage_zero_map (C : StableInfinityCategory.{0}) : IKStageZeroMap I C

variable {I V U M}

def_wanted native_IK_mapping_rectification (D : SpectrumHoClosedSource S R.replacements) (E : FreeZeroSphereSource)
    (H : IKInvariantExtension I V U M) (W : SphereIndexSource T S)
    (J : InvariantObjectComparison H (perfectSourceObject T W.index))
    (T₀ : IKStageZeroMap I (T.represented W.index)) (C : PerfectInfinityCategory.{0})
    (J_C : InvariantObjectComparison H C)
    (D_S : SpectrumTensorSource S R.replacements) (D_M : MotiveTensorSource V R.replacements M)
    (N : MotiveFunctorLinearity H.models D_S D_M)
    (Q_E : MotiveEvaluationSource D_M (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory))
    (Q_F : FunctorEvaluationSource H.models D_S D_M N
      (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory) Q_E) :
    IKComparisonRectification D E H W J T₀ C J_C D_S D_M N Q_E Q_F

theorem_wanted native_localizing_corepresentability (D : SpectrumHoClosedSource S R.replacements) (E : FreeZeroSphereSource)
    (H : IKInvariantExtension I V U M) (W : SphereIndexSource T S)
    (J : InvariantObjectComparison H (perfectSourceObject T W.index))
    (T₀ : IKStageZeroMap I (T.represented W.index)) (C : PerfectInfinityCategory.{0})
    (J_C : InvariantObjectComparison H C)
    (D_S : SpectrumTensorSource S R.replacements) (D_M : MotiveTensorSource V R.replacements M)
    (N : MotiveFunctorLinearity H.models D_S D_M)
    (Q_E : MotiveEvaluationSource D_M (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory))
    (Q_F : FunctorEvaluationSource H.models D_S D_M N
      (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory) Q_E)
    (C_map : IKComparisonRectification D E H W J T₀ C J_C D_S D_M N Q_E Q_F) : IsStableWeak S C_map.map

end MathlibExt.AlgebraicTopology.NativeIKCorepresentabilityModels

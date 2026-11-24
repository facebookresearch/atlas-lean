/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeMotiveLocalizationModels

/-!
# Independent native presheaf reflection and full functor-category requests

The local objects, native end maps, raw reflector augmentation and mapping
spectra are fixed before any K comparison. Completion is requested only
with perfect-target universality. No corepresentability is an input.
Sources: BGT arXiv:1001.2282v4 Sections 5--6/8; HTT Section 5.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeMotiveLocalizationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.SpectraSource
open StableInfinityCategoryModels StableSpectraInfinitySource NativeSpectralPresheafModels
open NativeMotivePresheafSources QuasicategoricalModels
open scoped Simplicial

def_wanted native_zero_stable_category : ZeroCategorySource

def_wanted native_perfect_completion (C : StableInfinityCategory.{0}) : PerfectCompletion C

variable (C : Type) [EnrichedCategory SymmetricSpectrum C]
  (S : SpectrumInfinitySource) (P : NativeSpectralPresheafModels.PresheafInfinitySource C S)

def_wanted native_presheaf_zero : PresheafZeroSource P

def_wanted native_presheaf_cofiber {E F Z : RawPresheaf C} (f : E ⟶ F) (t : E ⟶ Z)
    (zero : StableInfinityMappingSpaces.IsZeroObject P.category.toSSet (presheafVertex P Z)) :
    PresheafCofiber P f t

variable [HasInitial (RawPresheaf C)] [HasColimits (RawPresheaf C)]
  (H : EndFunctoriality C) (R : PresheafReplacements C S) (G : Set (RawMotiveGenerator (C := C)))

def_wanted native_motive_localization (small : SmallGeneratorPresentation P H R G) :
    MotiveLocalization P H R G

theorem_wanted native_motive_inverts_generator (M : MotiveLocalization P H R G)
    (g : RawMotiveGenerator (C := C)) (hg : g ∈ G) :
    IsEquivalenceEdge M.category.toSSet (M.reflector.app (Opposite.op ⦋1⦌) (presheafEdge P g.map))

def_wanted native_motive_full_mapping_comparison (M : MotiveLocalization P H R G) (E F : RawPresheaf C) :
    MotiveMappingComparison M E F

theorem_wanted native_motive_colimits (M : MotiveLocalization P H R G) : HasSmallColimits M.category.toSSet

theorem_wanted native_motive_full_functor_universal (M : MotiveLocalization P H R G)
    (D : StableInfinityCategory.{1}) (colimits : HasSmallColimits D.toSSet) : MotiveFunctorUniversal M D

end MathlibExt.AlgebraicTopology.NativeMotiveLocalizationModels

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeCompactSourceModels

/-!
# Native compact spectrum and stable-category skeleton construction

All compactness tests use actual coherent filtered colimits and their
canonical native comparisons. Homs and sphere normalization are fixed.
These are source construction requests; no K/motive equivalence is an input.

Source: BGT1001.2282v4 Sections2/5/7.2/8/9.1.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeCompactSourceModels

open NativeKParametrizedSource StableSpectraInfinitySource StableInfinityFilteredColimits
open StableInfinityCategoryModels
open scoped Cardinal

def_wanted native_compact_spectra_source (S : SpectrumInfinitySource) : CompactSpectraSource S

def_wanted native_additive_compact_skeleton (A : StableCategoryEnrichment) : CompactStableSkeleton A ℵ₀

def_wanted native_localizing_compact_skeleton (A : StableCategoryEnrichment) (k : UncountableRegularCardinal) :
  CompactStableSkeleton A k.value

theorem_wanted native_compact_sphere_category (A : StableCategoryEnrichment) (S : SpectrumInfinitySource)
    (P : CompactSpectraSource S) : IsCompactPerfectCategory A ℵ₀ P.small

def_wanted native_full_exact_functor_input (C : StableInfinityCategory.{0}) (D : PerfectInfinityCategory.{0}) :
  FullExactFunctorInput C D

end MathlibExt.AlgebraicTopology.NativeCompactSourceModels

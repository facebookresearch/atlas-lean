/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource

/-!
# Native full spectrum enrichment and coherent stable localization

The Hom carrier and all-level evaluation are independently defined by
the native function-spectrum and tensor/counit formulas. The coherent
source remains the native enriched nerve, with full functor categories.

Sources: Hovey--Shipley--Smith, Sections 2.2 and 3.1--3.4;
BGT1001.2282v4, Sections 2.1 and 2.3.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource

open StableSpectraInfinitySource

/-- Construct the native function-spectrum enrichment with all-level ordinary/composition normalization. -/
def_wanted native_spectrum_simplicial_enrichment : SpectrumSimplicialEnrichment

/-- Extend the original stable source to the entire actual coherent spectrum nerve. -/
def_wanted native_spectrum_coherent_localization (N : SpectrumSimplicialEnrichment)
    (S : SpectrumInfinitySource) : SpectrumCoherentLocalization N S

end MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource

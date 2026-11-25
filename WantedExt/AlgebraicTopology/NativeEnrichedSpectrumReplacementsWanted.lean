/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeEnrichedSpectrumReplacements

/-!
# Full native spectrum replacement construction

The actual source lifting/Omega-fibrancy tests, native Hom spaces and
all enriched augmentation equations are fixed independently of K.
Their point-set zero preservation concerns every original level simplex.

Source: Hovey--Shipley--Smith, Sections 3.1--3.4.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeEnrichedSpectrumReplacements

open NativeSpectraSimplicialSource StableSpectraInfinitySource

/-- Construct native enriched cofibrant/fibrant replacements with the original augmentation maps. -/
def_wanted native_enriched_spectrum_replacements (N : SpectrumSimplicialEnrichment)
    (S : SpectrumInfinitySource) : EnrichedSpectrumReplacements N S

end MathlibExt.AlgebraicTopology.NativeEnrichedSpectrumReplacements

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeKParametrizedSource

/-!
# Full enriched S/K source construction requests

Every Hom is fixed by actual full exact-functor cores or the native
function-spectrum space. The K constructor chooses its S-assembly and
full enriched action together, with explicit normalization on every
parameter simplex and every original S-diagonal.

Source: BGT1001.2282v4, Sections 2.1, 7.1 and 9.1.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeKParametrizedSource

open NativeSpectraSimplicialSource

/-- Construct the full stable-category enrichment from the original exact-functor cores. -/
def_wanted native_stable_category_enrichment : StableCategoryEnrichment

/-- Construct the actual S/K spectrum assembly and its full source-normalized enriched action. -/
def_wanted native_parametrized_k (A : StableCategoryEnrichment)
    (N : SpectrumSimplicialEnrichment) : ParametrizedKSource A N

end MathlibExt.AlgebraicTopology.NativeKParametrizedSource

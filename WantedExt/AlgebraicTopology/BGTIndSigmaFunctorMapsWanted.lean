/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.BGTIndSigmaFunctorMaps

/-!
# Source-normalized Ind and suspension functor maps

Source: BGT arXiv:1001.2282v4, Sections 2.4 and 5.1, Definition 9.1
and Proposition 9.5. These constructors use the actual filtered Yoneda
extension, native compact restriction and native Verdier cofiber maps.
No K-vanishing or corepresenting equivalence is supplied as input.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.BGTIndSigmaFunctorMaps

open StableInfinityCategoryModels StableInfinityFilteredColimits BGTIndKappaModels

/-- Extend the native exact functor through actual Ind and compact full categories. -/
def_wanted native_fkappa_functor_map (C D : StableInfinityCategory.{0})
    (k : UncountableRegularCardinal) (F : FKappaSource C k) (G : FKappaSource D k)
    (f : ExactFunctor C D) : FKappaFunctorMap F G f

/-- Apply the native Verdier cofiber universal property to that same source map. -/
def_wanted native_sigma_kappa_functor_map (C D : StableInfinityCategory.{0})
    (k : UncountableRegularCardinal) (S : SigmaKappaSource C k) (T : SigmaKappaSource D k)
    (f : ExactFunctor C D) : SigmaKappaFunctorMap S T f

end MathlibExt.AlgebraicTopology.BGTIndSigmaFunctorMaps

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.BGTCountableSwindleModels
public import MathlibExt.AlgebraicTopology.StableInfinityKSpectra

/-!
# Source countable-sum construction and swindle conclusions

Source: BGT arXiv:1001.2282v4, Definition 9.1 and Lemma 9.4.
The cone is the actual compact full subcategory of Ind-omega; the
countable sum is its actual universal coherent cocone, including all
native injections. Swindle equivalence and K-vanishing are conclusions.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.BGTCountableSwindleModels

open StableInfinityCategoryModels StableInfinityFilteredColimits
open BGTIndKappaModels StableInfinityKSpectra StableSpectraInfinitySource
open StableInfinityMappingSpaces

/-- Uncountability gives the actual countable-coproduct functor on F-kappa. -/
def_wanted native_cone_countable_sum (C : StableInfinityCategory.{0})
    (k : UncountableRegularCardinal) (F : FKappaSource C k) :
  CountableSumSource F.small

/-- Construct the native binary zero-corner pushout of identity and countable sum. -/
def_wanted native_identity_plus_sum (C : StableInfinityCategory.{0})
    (Q : CountableSumSource C) : IdentityPlusSumSource Q

/-- Reindexing the original countable colimit gives the full swindle natural equivalence. -/
theorem_wanted native_countable_swindle (C : StableInfinityCategory.{0})
    (Q : CountableSumSource C) (B : IdentityPlusSumSource Q) :
  IsSwindleEquivalence Q B

/-- Source Lemma 9.4 vanishing is measured in the actual native stable spectrum category. -/
theorem_wanted native_countable_sum_k_vanishing (C : StableInfinityCategory.{0})
    (Q : CountableSumSource C) (K : ConnectiveKConstruction)
    (S : SpectrumInfinitySource) :
  IsZeroObject S.category.toSSet (connectiveKVertex K S C)

end MathlibExt.AlgebraicTopology.BGTCountableSwindleModels

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.BGTIndKappaModels

/-!
# Native contravariant, Ind and Verdier source constructions

The outputs use the actual right slices and every relative mapping-space
fibre, the actual filtered representable closure, the actual compact full
subcategory, and the full exact-functor Verdier cofiber universal property.

Sources: Lurie, Higher Topos Theory, Sections 2.1--2.2 and 5.3.5;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2.4 and 5.1,
Definition 9.1 and Remark 9.2. K vanishing and universal-invariant
corepresentability are theorem conclusions in separate interfaces.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.BGTIndKappaModels

open StableInfinityCategoryModels StableInfinityFilteredColimits
open StableInfinityMappingSpaceMaps BGTContravariantPresheaves
open BGTVerdierQuotients

universe u

/-- Form the full right-fibration presheaf localization. -/
def_wanted native_contravariant_presheaves (C : SSet.{0})
    [SSet.Quasicategory C] : PresheafInfinitySource C

/-- The full Yoneda source is normalized by the actual right-fibration evaluation family. -/
def_wanted native_presheaf_yoneda (C : SSet.{0}) [SSet.Quasicategory C]
    (P : PresheafInfinitySource C) : PresheafYonedaSource C P

/-- Full faithfulness is the native map on all source mapping-space fibres. -/
theorem_wanted native_yoneda_fully_faithful (C : SSet.{0})
    [SSet.Quasicategory C] (P : PresheafInfinitySource C)
    (Y : PresheafYonedaSource C P) : IsFullyFaithful Y.map

/-- Construct the actual small stable Verdier cofiber of the specified full inclusion. -/
def_wanted native_stable_verdier_quotient
    (A B : StableInfinityCategory.{u}) (i : FullStableInclusion A B) :
  StableVerdierQuotient i

/-- Construct Ind-omega and its native kappa-compact full category and Yoneda inclusion. -/
def_wanted native_ind_kappa (C : StableInfinityCategory.{0})
    (k : UncountableRegularCardinal) : FKappaSource C k

/-- Construct the source suspension as the actual Verdier quotient F-kappa(C)/C. -/
def_wanted native_sigma_kappa (C : StableInfinityCategory.{0})
    (k : UncountableRegularCardinal) : SigmaKappaSource C k

end MathlibExt.AlgebraicTopology.BGTIndKappaModels

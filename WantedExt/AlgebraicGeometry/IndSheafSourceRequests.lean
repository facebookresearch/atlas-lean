/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
public import MathlibExt.AlgebraicGeometry.IndSheafSourceRequestsActualCompactPushforwardSource
public import MathlibExt.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageAdditive
public import MathlibExt.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageSource

/-!
# Source requests for the prescribed compact-support ind-sheaf construction

Only structural ordinary sheaf/Ind proofs are requested here. The
categories, compact support, continuous pushforward and compact-Yoneda
Kan extension are already fixed in the public source. The compact
pushforward source `actual_compact_pushforward_source` is proved in
`MathlibExt.AlgebraicGeometry.IndSheafSourceRequestsActualCompactPushforwardSource`.
The additivity statement `actual_ind_proper_image_additive` is proved in
`MathlibExt.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageAdditive`.
The ind-proper image source `actual_ind_proper_image_source` is proved in
`MathlibExt.AlgebraicGeometry.IndSheafSourceRequestsActualIndProperImageSource`.
These requests do not assume enhanced reconstruction or mixed-Hodge
admissibility.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2/3.2/3.3;
Kashiwara--Schapira, Ind-sheaves.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IndSheafSourceRequests

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels

/-- Actual compact-support sheaves, with their inherited hom-groups, form an abelian
category: kernels, cokernels and finite products of compactly supported sheaves are
compactly supported. Their ind-objects (with small filtered index categories) form an
abelian category, Kashiwara--Schapira, Categories and Sheaves, Theorem 8.6.5(i). -/
def_wanted actual_compact_sheaf_source (k : Type) [Field k] (X : TopCat.{0}) :
  CompactSheafSource k X

end WantedExt.AlgebraicGeometry.IndSheafSourceRequests

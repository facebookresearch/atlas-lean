/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels

/-!
# Source requests for the prescribed compact-support ind-sheaf construction

Only structural ordinary sheaf/Ind proofs are requested here. The
categories, compact support, continuous pushforward and compact-Yoneda
Kan extension are already fixed in the public source. These requests do
not assume enhanced reconstruction or mixed-Hodge admissibility.

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

/-- Continuous image of actual compact support gives compact proper-image generators. -/
theorem_wanted actual_compact_pushforward_source (k : Type) [Field k]
    (X Y : TopCat.{0}) [T2Space Y] (f : X ⟶ Y) : CompactPushforwardSource k f

/-- Extend the same actual compact generator functor by the native left Kan construction. -/
theorem_wanted actual_ind_proper_image_source (k : Type) [Field k]
    (X Y : TopCat.{0}) [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) : IndPushforwardSource k f P

/-- The native compact-generator extension has its ordinary additive structure. -/
theorem_wanted actual_ind_proper_image_additive (k : Type) [Field k]
    (X Y : TopCat.{0}) [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P) :
    (indProperImage k f P D).Additive

end WantedExt.AlgebraicGeometry.IndSheafSourceRequests

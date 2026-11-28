/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafAlphaBetaModels
public import MathlibExt.AlgebraicGeometry.IndSheafDerivedProperImageModels
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Native cochain alpha and its exact localization

The operator is the actual cochain action of the prescribed compact-Yoneda
alpha. Exactness concerns its action on the original quasi-isomorphisms.
The output is its native localization, not a selected realization functor.

Source: DK arXiv:1311.2374v2, Section 2.2; native cochains/localization:
Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IndSheafDerivedAlphaModels

open _root_.CategoryTheory
open CompactSupportIndSheaves IndSheafAlphaBetaModels IndSheafPushforwardModels

variable (k : Type) [Field k] (X : TopCat.{0}) [CompactSheafSource k X]
  (A : AlphaSource k X) [(alpha k X A).Additive]

local instance indAlphaPreadditive : Preadditive (IndSheaf k X) := Abelian.toPreadditive
local instance ordinaryAlphaPreadditive : Preadditive (OrdinarySheaf k X) :=
  Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

abbrev OrdinaryDerived := DerivedCategory (OrdinarySheaf k X)

/-- Cochain alpha followed by the original ordinary-sheaf quotient. -/
def alphaBeforeDeriving : CochainComplex (IndSheaf k X) ℤ ⥤ OrdinaryDerived k X :=
  beforeRightDerivation (A := IndSheaf k X) (B := OrdinarySheaf k X) (alpha k X A)

/-- Exactness refers to every actual original quasi-isomorphism. -/
structure ExactAlphaSource : Prop where
  inverts : (HomologicalComplex.quasiIso (IndSheaf k X) (.up ℤ)).IsInvertedBy
    (alphaBeforeDeriving k X A)

/-- The native exact derived alpha. -/
def derivedAlpha (S : ExactAlphaSource k X A) : IndDerived k X ⥤ OrdinaryDerived k X :=
  Localization.lift (alphaBeforeDeriving k X A) S.inverts DerivedCategory.Q

/-- The comparison is the native localization factorization on every cochain. -/
def derivedAlphaComparison (S : ExactAlphaSource k X A) :
    DerivedCategory.Q ⋙ derivedAlpha k X A S ≅ alphaBeforeDeriving k X A :=
  Localization.fac (alphaBeforeDeriving k X A) S.inverts DerivedCategory.Q

end MathlibExt.AlgebraicGeometry.IndSheafDerivedAlphaModels

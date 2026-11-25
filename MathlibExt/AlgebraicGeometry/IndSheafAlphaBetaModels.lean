/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The original alpha and beta of compact-support ind-sheaves

Alpha is the compact-Yoneda left Kan extension of the actual inclusion of
compact-supported ordinary sheaves. Beta is its native LEFT adjoint.
The existing ordinary-to-Ind embedding is iota; it is not renamed beta.
All three retain the prescribed ordinary/compact/Ind carriers and maps.

Source: D'Agnolo--Kashiwara arXiv:1311.2374v2, Section 2.2 (the three
functors beta, alpha, iota). Native adjoints/Kan extensions: Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IndSheafAlphaBetaModels

open _root_.CategoryTheory
open CompactSupportIndSheaves IndSheafCoefficientModels

variable (k : Type) [Field k] (X : TopCat.{0})

/-- The original compact generators, as ordinary sheaves. -/
def alphaGenerators : CompactSheaf k X ⥤ OrdinarySheaf k X :=
  compactAsOrdinary k X

/-- Existence only for the prescribed compact-generator extension. -/
structure AlphaSource : Prop where
  hasKan : (Ind.yoneda (C := CompactSheaf k X)).HasLeftKanExtension
    (alphaGenerators k X)

/-- Alpha computes the ordinary sheaf represented by the compact Ind diagram. -/
def alpha (S : AlphaSource k X) : IndSheaf k X ⥤ OrdinarySheaf k X :=
  letI := S.hasKan
  (Ind.yoneda (C := CompactSheaf k X)).leftKanExtension
    (alphaGenerators k X)

/-- The actual compact-generator comparison of alpha. -/
def alphaGeneratorUnit (S : AlphaSource k X) :
    alphaGenerators k X ⟶ Ind.yoneda ⋙ alpha k X S :=
  letI := S.hasKan
  (Ind.yoneda (C := CompactSheaf k X)).leftKanExtensionUnit
    (alphaGenerators k X)

/-- The condition that the functor `alpha k X S` from ind-sheaves to sheaves on $X$ is a right
adjoint, that is, has a left adjoint. -/
structure BetaSource (S : AlphaSource k X) : Prop where
  adjoint : (alpha k X S).IsRightAdjoint

/-- The native chosen LEFT adjoint of the prescribed alpha. -/
def beta (S : AlphaSource k X) (B : BetaSource k X S) :
    OrdinarySheaf k X ⥤ IndSheaf k X :=
  letI := B.adjoint
  (alpha k X S).leftAdjoint

/-- Beta is on the left, with its full native unit/counit on every object. -/
def betaAlphaAdjunction (S : AlphaSource k X) (B : BetaSource k X S) :
    beta k X S B ⊣ alpha k X S :=
  letI := B.adjoint
  Adjunction.ofIsRightAdjoint (alpha k X S)

/-- Iota retains the independent restricted-Yoneda construction. -/
def iota (S : OrdinaryIndSource k X) : OrdinarySheaf k X ⥤ IndSheaf k X :=
  ordinaryToInd k X S

/-- Normalization of iota refers to the prescribed original functors. -/
structure AlphaIotaSource (A : AlphaSource k X) (I : OrdinaryIndSource k X) where
  adjunction : alpha k X A ⊣ iota k X I

end MathlibExt.AlgebraicGeometry.IndSheafAlphaBetaModels

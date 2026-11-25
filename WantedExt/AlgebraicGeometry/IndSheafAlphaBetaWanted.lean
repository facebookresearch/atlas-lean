/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.IndSheafDerivedAlphaModels

/-!
# Source constructions of alpha, beta and their exact cochain action

These are structural requests for already prescribed native functors.
No enhanced reconstruction or holonomic comparison is a hypothesis.
Source: DK arXiv:1311.2374v2, Section 2.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IndSheafAlphaBetaWanted

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
open MathlibExt.AlgebraicGeometry.IndSheafAlphaBetaModels
open MathlibExt.AlgebraicGeometry.IndSheafDerivedAlphaModels

variable (k : Type) [Field k] (X : TopCat.{0}) [hHausdorff : T2Space X]
  [hLocallyCompact : LocallyCompactSpace X] [hCountableAtInfinity : SigmaCompactSpace X]

include hHausdorff hLocallyCompact hCountableAtInfinity

local instance sourceIndPreadditive [CompactSheafSource k X] :
    Preadditive (IndSheaf k X) := Abelian.toPreadditive

local instance sourceOrdinaryPreadditive : Preadditive (OrdinarySheaf k X) :=
  Abelian.toPreadditive

theorem_wanted actual_alpha_source : AlphaSource k X

theorem_wanted actual_beta_source (A : AlphaSource k X) : BetaSource k X A

def_wanted actual_alpha_iota_source (A : AlphaSource k X) (I : OrdinaryIndSource k X) :
  AlphaIotaSource k X A I

theorem_wanted actual_alpha_additive [CompactSheafSource k X] (A : AlphaSource k X) :
  (alpha k X A).Additive

theorem_wanted actual_alpha_exact [CompactSheafSource k X]
    (A : AlphaSource k X) [(alpha k X A).Additive] : ExactAlphaSource k X A

/-- **Full faithfulness of $\beta$ from sheaves to ind-sheaves.** Let $k$ be a field and $X$ a
Hausdorff, locally compact, σ-compact space. Let $\alpha$ be the functor from ind-sheaves
(ind-objects of compactly supported sheaves of $k$-vector spaces on $X$) to sheaves of $k$-vector
spaces given by the left Kan extension, along the Ind-Yoneda embedding, of the inclusion of
compactly supported sheaves (assumed to exist), and let $\beta$ be a left adjoint of $\alpha$
(assumed to exist). Then for every sheaf $F$ of $k$-vector spaces on $X$, the unit
$F \to \alpha \beta F$ of the adjunction is an isomorphism (equivalently, $\beta$ is fully
faithful). -/
theorem_wanted actual_beta_unit_iso (A : AlphaSource k X) (B : BetaSource k X A)
    (F : OrdinarySheaf k X) : IsIso ((betaAlphaAdjunction k X A B).unit.app F)

end WantedExt.AlgebraicGeometry.IndSheafAlphaBetaWanted

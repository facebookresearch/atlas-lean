/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification
public import MathlibExt.AlgebraicGeometry.PerfectoidSliceSites

/-!
# Normalized analytic-adic diamondification requests

The raw functor, marked-untilt comparison, v-sheafification and relation
kernel map are native prescribed constructions. Requests prove descent,
the exact marked-untilt formula, and a diamond presentation of that
actual sheaf. They do not assume an arbitrary analytic/diamond equivalence.

Source: Scholze, arXiv:1709.07343v4, Proposition 11.3(ii),
Definition 15.5 and Lemma 15.6.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticDiamondification

open CategoryTheory
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
open MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification
open MathlibExt.AlgebraicGeometry.PerfectoidDiamondModels
open MathlibExt.AlgebraicGeometry.PerfectoidSliceSites

/-- Let $p$ be a prime and $R \rightrightarrows X$ a representable pro-étale equivalence relation of
perfectoid spaces (`Relation p`), with quotient v-sheaf $X/R$, the coequalizer. Then the canonical
map from $R$ to the kernel pair $X \times_{X/R} X$ of the quotient map is an isomorphism. -/
public theorem_wanted relationToKernelIsIso (p : ℕ) [Fact p.Prime] (R : Relation p) :
    IsIso (relationToKernel p R)

/-- Let $p$ be a prime, $R$ an affine realization, $Y$ an analytic adic space and $P$ an affine
perfectoid space. Then `classComparison` is a bijection from the isomorphism classes of marked
untilts of $P$ over $Y$ (an affine untilt with an isomorphism of its tilt with $P$ and a map from
its realization to $Y$) to the value at $P$ of the raw diamond presheaf of $Y$; it sends a class to
its image under the unit of the left Kan extension. -/
public theorem_wanted markedUntiltingFormula (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) (P : Affine p) :
    Function.Bijective (classComparison (R := R) (Y := Y) P)

/-- Let $p$ be a prime, $R$ an affine realization and $Y$ an analytic adic space. Then the raw
diamond presheaf of $Y$, the left Kan extension along tilting of the presheaf of maps from
realizations of affine untilts to $Y$, is a sheaf for the v-topology on affine perfectoid spaces. -/
public theorem_wanted rawDiamondIsVSheaf (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) :
    Presheaf.IsSheaf (topology p) ((rawDiamondFunctor p R).obj Y)

/-- For a prime $p$, an affine realization $R$ and an analytic adic space $Y$: a diamond (a v-sheaf
with a representable pro-étale equivalence relation of perfectoid spaces whose quotient is
isomorphic to it) whose v-sheaf is the diamondification `diamondFunctor p R` of $Y$. -/
public def_wanted analyticDiamondPresentation (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) :
    {D : Diamond p // D.sheaf = (diamondFunctor p R).obj Y}

end WantedExt.AlgebraicGeometry.AnalyticDiamondification

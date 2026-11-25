/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites

/-!
# Actual analytic and diamond etale-site comparison requests

These compare the prescribed diamondification functor on the native
etale slice sites. Source etaleness is the original finite-Tate-ring
chart condition; target etaleness uses actual perfectoid affine
pullbacks. Continuity and equivalence are results, not source inputs.

Source: Scholze, arXiv:1709.07343v4, Lemma 15.6.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticDiamondEtale

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
open MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification
open MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites

/-- Let $p$ be a prime and $R$ an affine realization (the chosen affinoid models of affine
perfectoid untilts that define diamondification). Then the diamondification functor
`diamondFunctor p R` sends every étale morphism of analytic adic spaces (étale on affinoid charts)
to a representable étale morphism of v-sheaves. -/
public theorem_wanted etalePreservation (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) : PreservesEtale p R

/-- Let $p$ be a prime, $R$ an affine realization whose diamondification preserves étale morphisms
($h$), and $Y$ an analytic adic space. Then the functor `etaleDiamondification p R Y h`, from the
étale site of $Y$ to the representable-étale site of the diamond of $Y$, is an equivalence of
categories. -/
public theorem_wanted etaleEquivalence (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) (h : PreservesEtale p R) :
    (etaleDiamondification p R Y h).IsEquivalence

/-- Let $p$ be a prime, $R$ an affine realization whose diamondification preserves étale morphisms
($h$), and $Y$ an analytic adic space. Then the functor `etaleDiamondification p R Y h` is
continuous from the étale topology of $Y$ (jointly surjective families of étale maps) to the étale
topology of the diamond of $Y$ (jointly epimorphic families of representable étale maps):
restriction along it sends sheaves to sheaves. -/
public theorem_wanted etaleContinuity (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) (h : PreservesEtale p R) :
    (etaleDiamondification p R Y h).IsContinuous (analyticEtaleTopology p Y)
      (diamondEtaleTopology p ((diamondFunctor p R).obj Y))

/-- Let $p$ be a prime and $R$ an affine realization. Then `diamondFunctor p R` sends every finite
étale morphism of analytic adic spaces (finite étale over the whole inverse image of every affinoid
chart) to a representable finite étale morphism of v-sheaves (every pullback to an affine perfectoid
space is empty or a finite étale affine). -/
public theorem_wanted finiteEtalePreservation (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) : PreservesFiniteEtale p R

/-- Let $p$ be a prime, $R$ an affine realization whose diamondification preserves finite étale
morphisms ($h$), and $Y$ an analytic adic space. Then the functor
`finiteEtaleDiamondification p R Y h`, from finite étale spaces over $Y$ to representable finite
étale v-sheaves over the diamond of $Y$, is an equivalence of categories. -/
public theorem_wanted finiteEtaleEquivalence (p : ℕ) [Fact p.Prime]
    (R : AffineRealization p) (Y : AnalyticAdicSpace p) (h : PreservesFiniteEtale p R) :
    (finiteEtaleDiamondification p R Y h).IsEquivalence

end WantedExt.AlgebraicGeometry.AnalyticDiamondEtale

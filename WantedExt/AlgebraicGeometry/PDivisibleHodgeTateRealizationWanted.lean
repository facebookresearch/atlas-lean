/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PDivisibleHodgeTateRealizationModels
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Integral finite points and actual formal Hodge--Tate comparison

Scholze--Weinstein, arXiv:1211.6357v2, Sections 1--3 and 5.1;
Messing, The crystals associated to Barsotti--Tate groups, Chapter II.
Every request fixes original group points, finite dual augmentation
cotangents, nilpotent tangent tests and native scalar extensions.
The generic Tate inverse limit and finite Cartier duality are completed
source reuse; they are not requested again.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PDivisibleHodgeTateRealization

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AlgebraicallyClosedPadicTests
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
open MathlibExt.AlgebraicGeometry.PDivisibleLieModels
open MathlibExt.AlgebraicGeometry.PDivisibleFormalCartierCotangentModels
open MathlibExt.AlgebraicGeometry.PDivisibleHodgeTateRealizationModels

/-- $p$-adic completeness of the ring of integers: let $p$ be a prime and $C$ an algebraically
closed complete non-archimedean normed field extension of $\mathbb{Q}_p$ whose norm extends that of
$\mathbb{Q}_p$. Then $\mathcal{O}_C$, the elements of norm at most $1$, is $p$-adically complete and
separated. -/
public theorem_wanted integers_adic_complete
    (p : ℕ) [Fact p.Prime] (C : FieldTest p) :
    IsAdicComplete (Ideal.span {(p : integers p C)}) (integers p C)

/-- The formal cotangent module of a $p$-divisible group and its finite Cartier cotangents: let $p$
be a prime, $R$ a $p$-adically complete ring, $G$ a $p$-divisible group over $R$ with a Cartier dual
tower $D$, and $L$ a Lie model of $D$: a finite projective module $\omega$ representing the tangent
functor of $D$ on square-zero $p$-nilpotent tests (`LieModel`). Then for every $n$ there are an
identification, normalized on coordinates, of the tangent functor of the $n$-th level of $D$ with
the functor represented by $\omega_n$, the augmentation ideal modulo its square of the Cartier dual
of the $n$-th level of $G$, and maps $\omega \to \omega_n$ compatible with the tangent inclusions
and with the transition maps (`CotangentBridge`). -/
public def_wanted formalCartierCotangentBridge
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
    (L : LieModel p R D.group) : CotangentBridge p R G D L

/-- Finite projections of Tate points extend over $\mathcal{O}_C$: let $p$ be a prime and $C$ an
algebraically closed complete non-archimedean normed field extension of $\mathbb{Q}_p$ whose norm
extends that of $\mathbb{Q}_p$, and $G$ a $p$-divisible group over $\mathcal{O}_C$. Then each point
$x$ of the Tate module of $G$ over $C$ has, for every $n$, an $\mathcal{O}_C$-point of $G[p^n]$
extending its $n$-th projection, compatibly with the maps $G[p^{n+m}] \to G[p^m]$, with zero and
with addition (`IntegralProjectionSystem`). -/
public def_wanted integralTateFiniteProjections
    (p : ℕ) [Fact p.Prime] (C : FieldTest p)
    (G : PDivisibleGroup (IntegralScheme p C) p) : IntegralProjectionSystem p C G

/-- The Hodge–Tate map of a $p$-divisible group over $\mathcal{O}_C$: let $p$ be a prime and $C$ an
algebraically closed complete non-archimedean normed field extension of $\mathbb{Q}_p$ whose norm
extends that of $\mathbb{Q}_p$, $G$ a $p$-divisible group over $\mathcal{O}_C$ with a Cartier dual
tower $D$, $L$ a Lie model of $D$ with cotangent module $\omega$, $P$ a system of integral finite
projections of the Tate points of $G$ (`IntegralProjectionSystem`), and $B$ a comparison of $\omega$
with the finite Cartier cotangents (`CotangentBridge`). Then there is a $\mathbb{Z}_p$-linear map
$T_p G \to \omega$ sending each $x$ to an element whose projection at every level $n$ is the finite
dlog of the integral point $P_n(x)$, together with a $C$-linear map
$T_p G \otimes_{\mathbb{Z}_p} C \to \omega \otimes_{\mathcal{O}_C} C$ sending $c \otimes x$ to $c$
times the image of $x$ (`HodgeTateMap`). -/
public def_wanted geometricHodgeTateMap
    (p : ℕ) [Fact p.Prime] (C : FieldTest p)
    (G : PDivisibleGroup (IntegralScheme p C) p)
    (D : CartierDualTower p (integers p C) G)
    (L : LieModel p (integers p C) D.group)
    (P : IntegralProjectionSystem p C G)
    (B : CotangentBridge p (integers p C) G D L) : HodgeTateMap p C G D L P B

end WantedExt.AlgebraicGeometry.PDivisibleHodgeTateRealization

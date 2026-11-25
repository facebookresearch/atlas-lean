/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PDivisibleCartierGroupMaps

/-!
# Original Cartier-dual group map and F/V assembly

Finite maps already use the completed native Cartier functor. These
requests assemble their actual geometric towers, base changes and
relative scheme Frobenius. They require no inverse Frobenius on R.

Source: BBM82; Scholze--Weinstein1211.6357v2, Sections3.1 and4.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PDivisibleCartierGroupMaps

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
open MathlibExt.AlgebraicGeometry.PDivisibleCartierGroupMaps

/-- Let $p$ be a prime, $R$ a commutative ring, $f : G \to H$ a homomorphism of $p$-divisible groups
over $\operatorname{Spec} R$, and $D_G$, $D_H$ chosen Cartier dual towers of $G$ and $H$
($p$-divisible groups whose levels are identified with the Cartier duals of the levels of $G$ and
$H$). Then there is a homomorphism from the $p$-divisible group of $D_H$ to that of $D_G$ that, at
every level $n$ and under these identifications, is the Cartier dual of the level-$n$ map of $f$
(`DualHom`). -/
public def_wanted cartierDualTowerMap
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G H : PDivisibleGroup (Spec (.of R)) p)
    (f : MathlibExt.AlgebraicGeometry.PDivisibleGroupMaps.Hom p G H)
    (DG : CartierDualTower p R G) (DH : CartierDualTower p R H) :
    DualHom p R f DG DH

/-- Let $p$ be a prime, $R$ a commutative ring of characteristic $p$, $G$ a $p$-divisible group over
$\operatorname{Spec} R$ and $D_G$ a chosen Cartier dual tower of $G$. Then there are Frobenius and
Verschiebung data for $G$ normalized by Cartier duality (`CartierFrobeniusVerschiebung`): the
Frobenius twist $G^{(p)}$ with the relative Frobenius $F : G \to G^{(p)}$ and a Verschiebung
$V : G^{(p)} \to G$ with $V \circ F = p$ and $F \circ V = p$; a Cartier dual tower of $G^{(p)}$
whose levels are identified with the Frobenius base change of the levels of the dual of $G$; and the
Cartier dual maps of $F$ and $V$, the dual of $V$ being, under this identification, the relative
Frobenius of the dual of $G$. -/
public def_wanted cartierGroupFrobeniusVerschiebung
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (G : PDivisibleGroup (Spec (.of R)) p) (DG : CartierDualTower p R G) :
    CartierFrobeniusVerschiebung p R G DG

end WantedExt.AlgebraicGeometry.PDivisibleCartierGroupMaps

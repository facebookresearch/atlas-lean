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

/-- Assemble precisely the native finite dual maps of this original geometric group map. -/
public def_wanted cartierDualTowerMap
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (G H : PDivisibleGroup (Spec (.of R)) p)
    (f : MathlibExt.AlgebraicGeometry.PDivisibleGroupMaps.Hom p G H)
    (DG : CartierDualTower p R G) (DH : CartierDualTower p R H) :
    DualHom p R f DG DH

/-- Construct original Frobenius/Verschiebung with actual dual-Frobenius normalization. -/
public def_wanted cartierGroupFrobeniusVerschiebung
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    (G : PDivisibleGroup (Spec (.of R)) p) (DG : CartierDualTower p R G) :
    CartierFrobeniusVerschiebung p R G DG

end WantedExt.AlgebraicGeometry.PDivisibleCartierGroupMaps

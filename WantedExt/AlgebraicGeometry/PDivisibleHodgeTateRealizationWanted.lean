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

/-- The original norm-at-most-one ring of a complete p-adic field is p-adically complete. -/
public theorem_wanted integers_adic_complete
    (p : ℕ) [Fact p.Prime] (C : FieldTest p) :
    IsAdicComplete (Ideal.span {(p : integers p C)}) (integers p C)

/-- Compare finite Cartier cotangents with their original formal tangent inclusions. -/
public def_wanted formalCartierCotangentBridge
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
    (L : LieModel p R D.group) : CotangentBridge p R G D L

/-- Extend the original finite generic Tate points over the actual valuation ring O_C. -/
public def_wanted integralTateFiniteProjections
    (p : ℕ) [Fact p.Prime] (C : FieldTest p)
    (G : PDivisibleGroup (IntegralScheme p C) p) : IntegralProjectionSystem p C G

/-- Construct the source-normalized integral and rational formal Hodge--Tate maps. -/
public def_wanted geometricHodgeTateMap
    (p : ℕ) [Fact p.Prime] (C : FieldTest p)
    (G : PDivisibleGroup (IntegralScheme p C) p)
    (D : CartierDualTower p (integers p C) G)
    (L : LieModel p (integers p C) D.group)
    (P : IntegralProjectionSystem p C G)
    (B : CotangentBridge p (integers p C) G D L) : HodgeTateMap p C G D L P B

end WantedExt.AlgebraicGeometry.PDivisibleHodgeTateRealization

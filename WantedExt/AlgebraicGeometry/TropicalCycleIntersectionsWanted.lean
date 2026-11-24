/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.TropicalCycleIntersections

/-!
# Proper tropical intersection lifting

Osserman--Payne, *Lifting Tropical Intersections*, 1007.1314v3, Theorem 1.1.
The actual algebraic intersection ideal, valuation-vector closure and
polyhedral properness are fixed. We do not replace properness by a freely
named condition or assert lifting of arbitrary tropical set intersections.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.TropicalCycleIntersectionsWanted

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.IntegralTropicalCycles
open MathlibExt.AlgebraicGeometry.TropicalCycleIntersections
open MathlibExt.AlgebraicGeometry.ValuativeTropicalization

def_wanted weighted_presentation (K : Type) [Field K] [Valued K NNReal]
    [IsAlgClosed K] [CompleteSpace K] (_nontrivial : NontrivialValuation K)
    (n d : ℕ) (_dimension_le : d ≤ n)
    (I : Ideal (MathlibExt.AlgebraicGeometry.ValuativeTropicalization.CoordinateRing K n))
    (_pure : PureDimension K n I d) :
    {P : Presentation K n I // P.cycle.dimension = d}

theorem_wanted proper_intersection_lifts (K : Type) [Field K] [Valued K NNReal]
    [IsAlgClosed K] [CompleteSpace K] (_nontrivial : NontrivialValuation K)
    (n : ℕ) (I J : Ideal (MathlibExt.AlgebraicGeometry.ValuativeTropicalization.CoordinateRing K n))
    (A : Presentation K n I)
    (B : Presentation K n J) (w : RealSpace n) (_proper : ProperAt n A.cycle B.cycle w) :
    w ∈ tropicalizationOver (L := K) (intersectionIdeal K n I J)

end WantedExt.AlgebraicGeometry.TropicalCycleIntersectionsWanted

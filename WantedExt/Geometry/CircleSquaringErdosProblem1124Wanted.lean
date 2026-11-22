/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tarski's circle-squaring problem (Erdős Problem 1124)

Erdős Problem 1124 (Tarski): can a square and a circle of the same area be decomposed into a finite
number of congruent parts?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.MeasureTheory.Geometry.BanachTarski

@[expose] public section

namespace MathlibExt.Geometry.CircleSquaringErdosProblem1124Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1124, https://www.erdosproblems.com/1124 (status
PROVED). UnsolvedMath record UM-30007171 (`EP-1124`), dataset ulamai/UnsolvedMath v1.8.0.

The circle is the closed unit disc and the square is `[0, √π]²`, both of area `π`. Decomposition
into congruent parts is `MathlibExt`'s `FinitelyEquidecomposableByIsometries`: finitely many
pairwise disjoint pieces of arbitrary sets (Laczkovich's are not measurable) partitioning each
figure, the `i`-th pieces matched by an isometry of the plane. Any disc and square of equal area
are images of these two under one similarity followed by isometries, and conjugating by a
similarity keeps isometries isometries, so this instance is the general statement.
-/

/-- Erdős Problem 1124 (Tarski's circle-squaring problem): the closed unit disc and the closed
square `[0, √π]²` of the same area can be partitioned into finitely many pieces `A₁, …, A_k` and
`B₁, …, B_k` with each `Aᵢ` congruent to `Bᵢ`. Pieces are arbitrary sets; congruent means mapped
onto each other by an isometry of the plane. -/
def discSquareEquidecomposable : Prop :=
  MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.FinitelyEquidecomposableByIsometries
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    {x : EuclideanSpace ℝ (Fin 2) | ∀ j, 0 ≤ x j ∧ x j ≤ Real.sqrt Real.pi}

/--
Resolved true: Laczkovich proved that a disc and a square of the same area can be partitioned into
finitely many pieces that are pairwise translates, so in particular congruent;
erdosproblems.com/1124 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#1124, https://www.erdosproblems.com/1124 (status PROVED); resolution: M. Laczkovich,
Equidecomposability and discrepancy; a solution of Tarski's circle-squaring problem, J. Reine Angew.
Math. (1990), 77-117, a disc and a square of equal area are equidecomposable using translations only
(erdosproblems.com/1124), https://www.erdosproblems.com/1124.
-/
public theorem_wanted discSquareEquidecomposable_holds : discSquareEquidecomposable

end MathlibExt.Geometry.CircleSquaringErdosProblem1124Wanted

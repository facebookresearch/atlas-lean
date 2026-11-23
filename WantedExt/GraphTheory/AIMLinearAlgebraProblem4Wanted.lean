/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `AIM-LINEAR_ALGEBRA-0004`
# Positive and negative square energies of graphs (AimPL spectralhypergraph 1.4)

AimPL: Spectral graph and hypergraph theory: connections and applications, Section 1,
Problem 1.4, <http://aimpl.org/spectralhypergraph/1/>: for a connected graph `G` with adjacency
eigenvalues `λ₁ ≥ ⋯ ≥ λ_s ≥ 0 > λ_{s+1} ≥ ⋯ ≥ λ_n`, let `S⁺(G) = ∑_{i ≤ s} λᵢ²` and
`S⁻(G) = ∑_{i > s} λᵢ²`. Item 1: "Prove that `min {S⁺(G), S⁻(G)} ≥ n - 1`" (the conjecture of
Elphick, Farber, Goldberg and Wocjan). Items 2-4 (monotonicity along a sequence of added
complement edges) are not formalized.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.GraphTheory.AIMLinearAlgebraProblem4Wanted

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The positive square energy `S⁺(G)`: the sum of the squares of the nonnegative adjacency
eigenvalues of `G`. -/
noncomputable def positiveSquareEnergy (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ i, if 0 ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues i then
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ^ 2 else 0

/-- The negative square energy `S⁻(G)`: the sum of the squares of the negative adjacency
eigenvalues of `G`. -/
noncomputable def negativeSquareEnergy (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ i, if (G.isHermitian_adjMatrix ℝ).eigenvalues i < 0 then
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ^ 2 else 0

/-- AimPL Spectral graph and hypergraph theory, Problem 1.4, item 1: every connected graph on `n`
vertices has `min {S⁺(G), S⁻(G)} ≥ n - 1`. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected →
      (Fintype.card V : ℝ) - 1 ≤ min (positiveSquareEnergy G) (negativeSquareEnergy G)

-- Carried source audit `AIM-LINEAR_ALGEBRA-0004` (see the Moved/ record).

/--
Resolved true: Resolved for item 1, the formalized statement: Liu, Tang and Zhang proved
min{S⁺(G), S⁻(G)} ≥ n − 1 for every connected graph on n vertices (arXiv:2607.18031, July 2026),
and Hu, Liu and Wang use this theorem and determine the equality cases (arXiv:2608.17329). Items
2-4 of the source, not formalized, are open; the UnsolvedMath record reports a computer-found
counterexample to item 2 under the arbitrary-edge-order reading (unrefereed). Source: Y. Liu, Q.
Tang and S. Zhang, The positive and negative square-energy conjecture, arXiv:2607.18031 (July
2026), https://arxiv.org/abs/2607.18031; F.-T. Hu, Y.-Y. Liu and Y. Wang, Extremal graphs for a
conjecture on the square energy of graphs, arXiv:2608.17329 (August 2026),
https://arxiv.org/abs/2608.17329. Moved from
`OpenConjectures/GraphTheory/AIMLinearAlgebraProblem4`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.AIMLinearAlgebraProblem4Wanted

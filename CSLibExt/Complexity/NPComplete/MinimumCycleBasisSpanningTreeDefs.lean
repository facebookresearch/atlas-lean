/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CYCLE BASIS SPANNING TREE: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fourteenth edition), Journal of
Algorithms 6 (1985), 145-159, problem [2] MINIMUM CYCLE BASIS SPANNING TREE;
N. Deo, G. M. Prabhu and M. S. Krishnamoorthy, "Algorithms for generating fundamental cycles in
a graph", ACM Transactions on Mathematical Software 8(1) (1982), 26-42,
doi:10.1145/355984.355988.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCycleBasisSpanningTree

open ShortestTotalPathLengthSpanningTree (ShortestTotalPathLengthSpanningTreeInstance Graph
  WellFormed)

open Classical in
/-- The sum of `T.dist u v + 1` over the edges `{u, v}` of `G` that are not edges of `T` (each
once, as `u < v`); `T.dist` is `0` between vertices `T` does not connect. When `T` is a
spanning tree of `G`, this is the total length of the fundamental cycles of `G` with respect
to `T`. -/
noncomputable def fundamentalCycleLength {n : ℕ} (G T : SimpleGraph (Fin n)) : ℕ :=
  ∑ u : Fin n, ∑ v ∈ Finset.univ.filter (fun v => u < v ∧ G.Adj u v ∧ ¬ T.Adj u v),
    (T.dist u v + 1)

/-- A spanning tree `T ≤ G` whose fundamental cycles have total length at most `B`. -/
def MinimumCycleBasisSpanningTreeFeasible (i : ShortestTotalPathLengthSpanningTreeInstance) :
    Prop :=
  ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ T.IsTree ∧
    fundamentalCycleLength (Graph i) T ≤ i.2.2

open Classical in
/-- MINIMUM CYCLE BASIS SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def minimumCycleBasisSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestTotalPathLengthSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCycleBasisSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumCycleBasisSpanningTree

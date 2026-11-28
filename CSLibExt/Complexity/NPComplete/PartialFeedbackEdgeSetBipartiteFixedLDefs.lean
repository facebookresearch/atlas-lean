/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL FEEDBACK EDGE SET for bipartite graphs with fixed `L ≥ 4`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT9] PARTIAL
FEEDBACK EDGE SET, comment;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th
Annual ACM Symposium on Theory of Computing (1978), 253-264,
doi:10.1145/800133.804355.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.PartialFeedbackEdgeSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialFeedbackEdgeSetBipartiteFixedL

/-- An instance for a fixed cycle-length bound: vertex count `n` (vertices `Fin n`), edge list,
bound `K`. -/
abbrev BipartiteFixedLInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The PARTIAL FEEDBACK EDGE SET instance given by `i` and the cycle-length bound `L`. -/
abbrev withBound (i : BipartiteFixedLInstance) (L : ℕ) :
    PartialFeedbackEdgeSet.PartialFeedbackEdgeSetInstance :=
  (i.1, i.2.1, i.2.2, L)

/-- Well-formedness for the fixed bound `L`: the PARTIAL FEEDBACK EDGE SET instance
`withBound i L` is well formed and its graph is bipartite. -/
def WellFormed (i : BipartiteFixedLInstance) (L : ℕ) : Prop :=
  PartialFeedbackEdgeSet.WellFormed (withBound i L) ∧
    (PartialFeedbackEdgeSet.Graph (withBound i L)).IsBipartite

open Classical in
/-- PARTIAL FEEDBACK EDGE SET for bipartite graphs with the cycle-length bound fixed to `L`, as
a decision problem over bitstrings. -/
noncomputable def bipartiteFixedLDec (L : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := BipartiteFixedLInstance) x with
  | some i => decide (WellFormed i L ∧
      PartialFeedbackEdgeSet.PartialFeedbackEdgeSetFeasible (withBound i L))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartialFeedbackEdgeSetBipartiteFixedL

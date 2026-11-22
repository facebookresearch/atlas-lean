/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL FEEDBACK EDGE SET for bipartite graphs with fixed `L ≥ 4` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT9] PARTIAL
FEEDBACK EDGE SET, comment;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th
Annual ACM Symposium on Theory of Computing (1978), 253-264,
doi:10.1145/800133.804355.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import WantedExt.Complexity.NPComplete.PartialFeedbackEdgeSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialFeedbackEdgeSetBipartiteFixedL

/-!
# PARTIAL FEEDBACK EDGE SET for bipartite graphs with fixed `L ≥ 4` is NP-complete

For a fixed constant `L ≥ 4`: given a bipartite graph `G = (V, E)` and a positive integer
`K ≤ |E|`, is there a subset `E' ⊆ E` with `|E'| ≤ K` such that `E'` contains at least one edge
from every circuit of length `L` or less in `G`?

Garey and Johnson's comment on [GT9]: "Remains NP-complete for any fixed L ≥ 3 and for
bipartite graphs (with fixed L ≥ 4)." This is the restriction of PARTIAL FEEDBACK EDGE SET
(`WantedExt.Complexity.NPComplete.PartialFeedbackEdgeSetWanted`) to bipartite graphs, with `L`
no longer part of the instance. The instance is the graph and `K`; `withBound i L` appends the
fixed `L` to obtain an instance of that problem, whose `WellFormed` (including the source's
`L ≤ |V|`) and `PartialFeedbackEdgeSetFeasible` are reused unchanged, and `WellFormed` here adds
that the graph is bipartite (Mathlib's `SimpleGraph.IsBipartite`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PARTIAL FEEDBACK EDGE SET for bipartite graphs is NP-complete for every fixed `L ≥ 4`.**
Source: Garey and Johnson (1979), [GT9], comment; Yannakakis (1978). -/
public theorem_wanted partialFeedbackEdgeSetBipartiteFixedL_npComplete (L : ℕ) (hL : 4 ≤ L) :
    bipartiteFixedLDec L ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L' : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L' ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L' (bipartiteFixedLDec L)

end MetaMathlibExt.Complexity.NPComplete.PartialFeedbackEdgeSetBipartiteFixedL

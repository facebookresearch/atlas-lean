/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS with unit weights is NP-complete on graphs of maximum degree `k`, for
every fixed `k ≥ 4`

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS,
pp. 208-209 (the problem; NP-complete with equal edge weights, even for planar graphs);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (unweighted STEINER TREE IN GRAPHS is NP-complete for
degree-`k` graphs, `k` fixed, and for grid graphs, the latter citing Garey and Johnson 1977);
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM J.
Appl. Math. 32 (1977), 826-834, doi:10.1137/0132071.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitSteinerTreeBoundedDegree

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS with unit weights on graphs of maximum degree `k` is NP-complete

Fix `k`. INSTANCE: a graph `G = (V, E)` in which no vertex has degree exceeding `k`, a subset
`R ⊆ V`, and a positive integer bound `B`. QUESTION: is there a subtree of `G` that includes all
the vertices of `R` and has at most `B` edges?

This is STEINER TREE IN GRAPHS ([ND12], `SteinerTreeWanted`) with all edge weights equal to `1`
(the unweighted problem of Johnson's Table 1), restricted to degree-`k` graphs. Johnson's Table 1
records the problem as NP-complete for degree-`k` graphs with `k` fixed, and for grid graphs
(subgraphs of the two-dimensional rectilinear grid) with reference to Garey and Johnson (1977). A
grid graph has maximum degree at most `4`, so the problem is NP-complete for every fixed
`k ≥ 4`, which is the theorem below (one decision problem per `k`). Smaller `k` are not claimed.

The instance type and the question are those of `SteinerTreeWanted`
(`SteinerTree.SteinerTreeInstance`: a vertex count, weighted edges `(u, v, w)`, the terminals `R`
and the bound `B`; `SteinerTree.SteinerTreeFeasible`: some sublist of the edges of total weight at
most `B` connects all terminals), as in `SteinerTreeSplitGraphsWanted`. The restriction is added to
`WellFormed`: the parent's well-formedness, every weight equal to `1`, every vertex of the graph of
all edges (`SteinerTree.Graph i i.2.1`) of degree at most `k` (Mathlib's `SimpleGraph.degree`, as
in `SimpleMaxCutDegreeThreeWanted`),
and `0 < B`. With unit weights the total weight of an edge set is its number of edges, and a
connecting edge set contains a tree on the terminals with no more edges, so the question asks for
a subtree of `G` containing `R` with at most `B` edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance for the degree bound `k`: a well-formed STEINER TREE IN GRAPHS
instance with every edge weight `1`, every vertex of degree at most `k`, and `0 < B`. -/
def WellFormed (k : ℕ) (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (∀ v, (SteinerTree.Graph i i.2.1).degree v ≤ k) ∧
    0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS with unit weights on graphs of maximum degree `k`, as a decision
problem over bitstrings. -/
noncomputable def unitSteinerTreeBoundedDegreeDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed k i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN GRAPHS with unit weights is NP-complete on graphs of maximum degree `k`,
for every fixed `k ≥ 4`.** Source: Garey and Johnson (1979), [ND12]; Johnson (1985), Table 1;
Garey and Johnson (1977). -/
public theorem_wanted unitSteinerTreeBoundedDegree_npComplete (k : ℕ) (hk : 4 ≤ k) :
    unitSteinerTreeBoundedDegreeDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (unitSteinerTreeBoundedDegreeDec k)

end MetaMathlibExt.Complexity.NPComplete.UnitSteinerTreeBoundedDegree

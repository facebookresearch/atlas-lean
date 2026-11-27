/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for grid graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS;
D. S. Johnson, "The NP-completeness column: an ongoing guide" (sixteenth edition), Journal of
Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Grid", column
"StTree" for (unweighted) STEINER TREE IN GRAPHS: "N [35]");
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32 (1977), 826-834, doi:10.1137/0132071.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeGridGraphs

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS (unit weights) for grid graphs is NP-complete

INSTANCE: a grid graph `G = (V, E)`, i.e. a subgraph of the two-dimensional rectilinear grid, a
subset `R ⊆ V`, and a positive integer `K`. QUESTION: is there a subtree of `G` that includes
all the vertices of `R` and has at most `K` edges?

This is STEINER TREE IN GRAPHS ([ND12], `SteinerTreeWanted`) with all edge weights equal to 1,
restricted to grid graphs, the entry of Johnson's Table 1 (sixteenth column) for (unweighted)
STEINER TREE IN GRAPHS on the class "Grid", whose text defines grid graphs as "subgraphs of the
two-dimensional rectilinear grid". The instance type, `SteinerTree.WellFormed` and
`SteinerTree.SteinerTreeFeasible` (a sublist `T` of the edges of total weight at most `K` in
which all vertices of `R` are pairwise reachable; a subtree with these properties exists exactly
when such a `T` does, by taking a spanning tree of the component of `R`) are the parent's,
unchanged. `WellFormed` adds:

* unit weights: every edge has weight 1, as in `SteinerTreeSplitGraphsWanted`, so the total
  weight of `T` is its number of edges;
* the grid restriction: the graph of the instance is isomorphic to a (not necessarily induced)
  subgraph of the grid `ℤ × ℤ`, the box product of two copies of the Hasse graph of `ℤ`
  (`SimpleGraph.IsContained`, as in `DominatingSetPartialGridWanted`);
* `0 < K`, the source's positive bound;
* `0 < n`: the graph has a vertex. With no vertices the parent's feasibility condition would hold
  vacuously (no terminals to connect, `T = []`), although the empty graph has no subtree.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (simple weighted edge list, terminals listed
once and below `n`), every edge weight is 1, the graph is a subgraph of the grid up to
isomorphism, `K` is positive, and the graph has a vertex. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (SteinerTree.Graph i i.2.1).IsContained (SimpleGraph.hasse ℤ □ SimpleGraph.hasse ℤ) ∧
    0 < i.2.2.2 ∧ 0 < i.1

open Classical in
/-- STEINER TREE IN GRAPHS with unit weights on grid graphs as a decision problem over
bitstrings. -/
noncomputable def steinerTreeGridGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN GRAPHS with unit weights is NP-complete for grid graphs.** Source: Garey
and Johnson (1979), [ND12]; Johnson, NP-completeness column (1985), Table 1; Garey and Johnson
(1977). -/
public theorem_wanted steinerTreeGridGraphs_npComplete :
    steinerTreeGridGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeGridGraphsDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeGridGraphs

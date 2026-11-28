/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED BANDWIDTH for rooted directed trees with out-degree at most 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT41] DIRECTED BANDWIDTH, p. 200
(comment: "Remains NP-complete for rooted directed trees with maximum in-degree 1 and maximum
out-degree at most 2.");
M. R. Garey, R. L. Graham, D. S. Johnson, and D. E. Knuth, "Complexity results for bandwidth
minimization", SIAM Journal on Applied Mathematics 34 (1978), 477-495, doi:10.1137/0134037,
Section 9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedBandwidthRootedTreesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedBandwidthRootedTrees

open MetaMathlibExt.Complexity.NPComplete.DirectedBandwidth (DirectedBandwidthInstance)

/-!
# DIRECTED BANDWIDTH for rooted directed trees with out-degree at most 2 is NP-complete

INSTANCE: a rooted directed tree `G = (V, A)` with maximum in-degree 1 and maximum out-degree at
most 2, and a positive integer `K ≤ |V|`. QUESTION: is there a one-to-one function
`f : V → {1, 2, ..., |V|}` such that, for all `(u, v) ∈ A`, `f(u) < f(v)` and
`f(v) - f(u) ≤ K`?

This is DIRECTED BANDWIDTH ([GT41], `DirectedBandwidthWanted`) restricted as in the entry's
comment. The instance type, `DirectedBandwidth.WellFormed` (arcs in range, no self-loops, no
repeated arcs, acyclic, `0 < K ≤ |V|`) and `DirectedBandwidth.DirectedBandwidthFeasible` are the
parent's, unchanged; `WellFormed` adds the restriction:

* tree: the underlying undirected graph, Mathlib's `Digraph.toSimpleGraphInclusive` of the
  digraph `Graph i` (an edge `{u, v}` whenever `u → v` or `v → u` is an arc), is a tree
  (`SimpleGraph.IsTree`: connected, which needs at least one vertex, and acyclic);
* every vertex has in-degree at most 1 and out-degree at most 2, counted as the numbers of
  distinct in- and out-neighbours.

These conditions describe exactly the rooted directed trees of the comment with its degree
bounds: the parent's acyclicity rules out a pair of opposite arcs, so the arcs correspond one to
one to the `|V| - 1` tree edges; as each in-degree is at most 1, exactly one vertex, the root,
has in-degree 0, and following the unique in-arcs backwards from any vertex reaches the root, so
every arc points away from the root.

Garey, Graham, Johnson and Knuth (Section 9, Theorem) state the result for the reversed
orientation: an oriented tree (out-degree at most 1, no cycles) with no vertex of in-degree
greater than 2. Reversing every arc and replacing `f` by `|V| + 1 - f` maps the instances of one
form to those of the other and preserves the answer, so the two forms are the same problem up to
this renaming.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DIRECTED BANDWIDTH is NP-complete for rooted directed trees with maximum in-degree 1 and
maximum out-degree at most 2.** Source: Garey and Johnson (1979), [GT41], comment; Garey,
Graham, Johnson and Knuth (1978), Section 9. -/
public theorem_wanted directedBandwidthRootedTrees_npComplete :
    directedBandwidthRootedTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedBandwidthRootedTreesDec

end MetaMathlibExt.Complexity.NPComplete.DirectedBandwidthRootedTrees

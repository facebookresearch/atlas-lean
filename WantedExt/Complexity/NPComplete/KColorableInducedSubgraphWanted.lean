/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-COLORABLE INDUCED SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT21] INDUCED SUBGRAPH
WITH PROPERTY Π (comment);
J. M. Lewis and M. Yannakakis, "The node-deletion problem for hereditary properties is
NP-complete", Journal of Computer and System Sciences 20 (1980), 219-230,
doi:10.1016/0022-0000(80)90060-4;
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM K-COLORABLE INDUCED SUBGRAPH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import WantedExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KColorableInducedSubgraph

/-!
# K-COLORABLE INDUCED SUBGRAPH is NP-complete

For a fixed positive integer `k`:

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a subset `V' ⊆ V` with `|V'| ≥ K` such that the subgraph of `G` induced by
`V'` is `k`-colorable, i.e. has a coloring with at most `k` colors?

This is the decision version of MAXIMUM K-COLORABLE INDUCED SUBGRAPH from the Crescenzi-Kann
compendium, where `k` is a fixed constant; for `k = 1` it is INDEPENDENT SET. Being
`k`-colorable holds for arbitrarily large graphs (edgeless graphs), does not hold for all graphs
(the complete graph on `k + 1` vertices) and is hereditary, so the comment to [GT21] (Lewis and
Yannakakis) makes the problem NP-hard; `V'` with a coloring is a polynomial certificate.

This is INDUCED SUBGRAPH WITH PROPERTY Π ([GT21], `InducedSubgraphWithPropertyPiWanted`) for
the property "`k`-colorable", so the instance type, `InducedSubgraphWithPropertyPi.WellFormed`
(a simple edge list on `Fin n` and `0 < K ≤ |V|`, the bound of [GT21]) and
`InducedSubgraphWithPropertyPi.InducedSubgraphWithPropertyPiFeasible` (some injective
`f : Fin m ↪ Fin n` with `m ≥ K` whose induced subgraph `G.comap f` has the property) are
reused unchanged. `k`-colorability is Mathlib's `SimpleGraph.Colorable k`.

The [GT21] theorem assumes that the property can be tested in polynomial time, which fails for
`k ≥ 3` unless P = NP; the statement below is unconditional for each `k ≥ 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The graph property "`k`-colorable": a graph on `Fin m` has a coloring with at most `k`
colors (`SimpleGraph.Colorable k`). -/
def colorableProperty (k : ℕ) : InducedSubgraphWithPropertyPi.GraphProperty :=
  fun _ G => G.Colorable k

/-- K-COLORABLE INDUCED SUBGRAPH, for a fixed `k`, as a decision problem over bitstrings:
INDUCED SUBGRAPH WITH PROPERTY Π for `Π` = `k`-colorable. -/
noncomputable def kColorableInducedSubgraphDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  InducedSubgraphWithPropertyPi.inducedSubgraphWithPropertyPiDec (colorableProperty k)

/-- **K-COLORABLE INDUCED SUBGRAPH is NP-complete** for every fixed `k ≥ 1`. Source: Garey and
Johnson (1979), [GT21]; Lewis and Yannakakis (1980); Crescenzi and Kann, MAXIMUM K-COLORABLE INDUCED
SUBGRAPH. -/
public theorem_wanted kColorableInducedSubgraph_npComplete (k : ℕ) (hk : 0 < k) :
    kColorableInducedSubgraphDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (kColorableInducedSubgraphDec k)

end MetaMathlibExt.Complexity.NPComplete.KColorableInducedSubgraph

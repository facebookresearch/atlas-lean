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
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem [GT38]
MAXIMUM K-COLORABLE INDUCED SUBGRAPH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KColorableInducedSubgraph

/-!
# K-COLORABLE INDUCED SUBGRAPH is NP-complete

For a fixed positive integer `k`:

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a subset `V' ⊆ V` with `|V'| ≥ K` such that the subgraph of `G` induced by
`V'` is `k`-colorable, i.e. has a coloring with at most `k` colors?

This is the decision version of MAXIMUM K-COLORABLE INDUCED SUBGRAPH from the Crescenzi-Kann
compendium ([GT38]), where `k` is a fixed constant; for `k = 1` it is INDEPENDENT SET. The bound
`K ≤ |V|` is the one of Garey and Johnson's INDUCED SUBGRAPH WITH PROPERTY Π ([GT21]). Being
`k`-colorable holds for arbitrarily large graphs (edgeless graphs), does not hold for all graphs
(the complete graph on `k + 1` vertices) and is hereditary, so the comment to [GT21] (Lewis and
Yannakakis) makes the problem NP-hard; `V'` with a coloring is a polynomial certificate.

`k`-colorability is Mathlib's `SimpleGraph.Colorable k`, and the induced subgraph is Mathlib's
`SimpleGraph.induce`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev KColorableInducedSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : KColorableInducedSubgraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |V|`. -/
def WellFormed (i : KColorableInducedSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set `V'` of at least `K` vertices induces a `k`-colorable subgraph of `G`. -/
def KColorableInducedSubgraphFeasible (k : ℕ) (i : KColorableInducedSubgraphInstance) :
    Prop :=
  ∃ V' : Finset (Fin i.1), i.2.2 ≤ V'.card ∧
    ((Graph i).induce (V' : Set (Fin i.1))).Colorable k

open Classical in
/-- K-COLORABLE INDUCED SUBGRAPH, for a fixed `k`, as a decision problem over bitstrings. -/
noncomputable def kColorableInducedSubgraphDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KColorableInducedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ KColorableInducedSubgraphFeasible k i)
  | none => false

/-- **K-COLORABLE INDUCED SUBGRAPH is NP-complete** for every fixed `k ≥ 1`. Source: Garey and
Johnson (1979), [GT21]; Lewis and Yannakakis (1980); Crescenzi and Kann, [GT38]. -/
public theorem_wanted kColorableInducedSubgraph_npComplete (k : ℕ) (hk : 0 < k) :
    kColorableInducedSubgraphDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (kColorableInducedSubgraphDec k)

end MetaMathlibExt.Complexity.NPComplete.KColorableInducedSubgraph

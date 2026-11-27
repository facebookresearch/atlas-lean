/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF (K4, CLAW, DIAMOND)-FREE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
P. A. Golovach, M. Johnson, D. Paulusma and J. Song, "A survey on the computational complexity of
coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, Section 3, proof of Theorem 21 (i) 2 (arXiv:1407.1482v8);
ISGCI (Information System on Graph Classes and their Inclusions), class `(K_4, claw, diamond)`-free
(gc_919), problem 3-Colourability: NP-complete [Král' et al. 2001].
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Star
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityK4ClawDiamondFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# 3-COLORABILITY OF (K4, CLAW, DIAMOND)-FREE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with no induced subgraph isomorphic to
`K_4`, to the claw `K_{1,3}`, or to the diamond `K_4 - e`.
QUESTION: is `G` 3-colorable, that is, is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)`
for every edge `uv`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) with `K = 3`,
restricted to `(K_4, claw, diamond)`-free graphs. Induced subgraphs are Mathlib's
`SimpleGraph.IsIndContained` (an injective map that preserves adjacency and non-adjacency). The
three forbidden graphs, on `Fin 4`:
* `K_4`: every copy of `K_4` is induced, so `K_4`-freeness is Mathlib's
  `SimpleGraph.CliqueFree 4` (no 4-clique);
* the claw `K_{1,3}`: Mathlib's star `SimpleGraph.starGraph (0 : Fin 4)` (center `0`, leaves
  `1, 2, 3`);
* the diamond `K_4 - e`: the complete graph on `Fin 4` with the edge `{0, 1}` deleted,
  `(⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}`.

Král', Kratochvíl, Tuza and Woeginger show that 3-COLORABILITY is NP-complete for
`(K_4, claw, diamond)`-free graphs (as recorded by Golovach, Johnson, Paulusma and Song in the
proof of their Theorem 21); ISGCI lists 3-Colourability on this class (gc_919) as NP-complete,
citing Král' et al.

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable K`). The
restriction adds `K = 3` and the three exclusions to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `K = 3`
whose graph has no `K_4`, no induced claw `K_{1,3}` and no induced diamond `K_4 - e`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ (Graph i).CliqueFree 4 ∧
    ¬ (SimpleGraph.starGraph (0 : Fin 4)).IsIndContained (Graph i) ∧
    ¬ ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}).IsIndContained (Graph i)

open Classical in
/-- 3-COLORABILITY OF (K4, CLAW, DIAMOND)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityK4ClawDiamondFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **3-COLORABILITY OF (K4, CLAW, DIAMOND)-FREE GRAPHS is NP-complete.** Source: Garey and
Johnson (1979), [GT4]; Král', Kratochvíl, Tuza and Woeginger (2001). -/
public theorem_wanted threeColorabilityK4ClawDiamondFree_npComplete :
    threeColorabilityK4ClawDiamondFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityK4ClawDiamondFreeDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityK4ClawDiamondFree

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF GRAPHS OF GIRTH AT LEAST 9 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
M. Kamiński and V. V. Lozin, "Coloring edges and vertices of graphs without short or long
cycles", Contributions to Discrete Mathematics 2 (2007), 61-66, doi:10.55016/ojs/cdm.v2i1.61890,
Theorem 2.3;
T. Emden-Weinert, S. Hougardy and B. Kreuter, "Uniquely colourable graphs and the hardness of
colouring graphs of large girth", Combinatorics, Probability and Computing 7 (1998), 375-386,
doi:10.1017/S0963548398003678;
P. A. Golovach, M. Johnson, D. Paulusma and J. Song, "A survey on the computational complexity of
coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, Section 2.1 and Theorem 4 (arXiv:1407.1482v8);
ISGCI (Information System on Graph Classes and their Inclusions), class girth >=9 (gc_1225),
problem 3-Colourability: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityGirthNine

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# 3-COLORABILITY OF GRAPHS OF GIRTH AT LEAST 9 is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` of girth at least 9, that is, with no
cycle on fewer than 9 vertices.
QUESTION: is `G` 3-colorable, that is, is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)`
for every edge `uv`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) with `K = 3`,
restricted to graphs of girth at least 9 (ISGCI: "A graph has girth >=9 if it has no cycles with
less than 9 vertices"). The girth is Mathlib's extended girth `SimpleGraph.egirth`, the least
length of a cycle, which is `⊤` for an acyclic graph; a cycle has as many vertices as edges, so
`9 ≤ (Graph i).egirth` says exactly that every cycle has at least 9 vertices. Kamiński and Lozin,
Theorem 2.3: "For every natural k, g ≥ 3, vertex k-colorability is NP-hard in the class of graphs
of girth at least g"; Emden-Weinert, Hougardy and Kreuter had proved the stronger statement with
the maximum degree also bounded (Golovach, Johnson, Paulusma and Song, Theorem 4, record both).
The case `k = 3`, `g = 9` is this problem; membership in NP is immediate (a coloring is a
certificate).

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable K`). The
restriction adds `K = 3` and girth at least 9 to well-formedness.

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
whose graph has girth at least 9 (every cycle has length at least 9). -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ 9 ≤ (Graph i).egirth

open Classical in
/-- 3-COLORABILITY OF GRAPHS OF GIRTH AT LEAST 9 as a decision problem over bitstrings. -/
noncomputable def threeColorabilityGirthNineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **3-COLORABILITY OF GRAPHS OF GIRTH AT LEAST 9 is NP-complete.** Source: Garey and Johnson
(1979), [GT4]; Kamiński and Lozin (2007), Theorem 2.3; Emden-Weinert, Hougardy and Kreuter
(1998). -/
public theorem_wanted threeColorabilityGirthNine_npComplete :
    threeColorabilityGirthNineDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityGirthNineDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityGirthNine

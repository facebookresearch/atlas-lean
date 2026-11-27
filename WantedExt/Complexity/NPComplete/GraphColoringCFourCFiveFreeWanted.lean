/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY ON (C₄, C₅)-FREE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
D. Král', J. Kratochvíl, Zs. Tuza, and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
M. Kamiński and V. V. Lozin, "Coloring edges and vertices of graphs without short or long
cycles", Contributions to Discrete Mathematics 2 (2007), 61-66, doi:10.55016/ojs/cdm.v2i1.61890;
P. A. Golovach, M. Johnson, D. Paulusma, and J. Song, "A survey on the computational complexity
of coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, arXiv:1407.1482, Theorem 21 (i) 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringCFourCFiveFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# GRAPH K-COLORABILITY ON (C₄, C₅)-FREE GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) with no induced subgraph isomorphic
to the cycle `C₄` and none isomorphic to the cycle `C₅`, and a positive integer `K ≤ |V|`.
QUESTION: is `G` `K`-colorable, i.e. is there a map `c : V → {1, …, K}` with `c(u) ≠ c(v)` for
every edge `uv`?

This is GRAPH K-COLORABILITY restricted to the class of `(C₄, C₅)`-free graphs (ISGCI class
`gc_367`). Král', Kratochvíl, Tuza, and Woeginger show that 3-colouring is NP-complete for graphs
of girth at least `g`, for every fixed `g ≥ 3` (Kamiński and Lozin extend this to `k`-colouring for
every `k ≥ 3`). Graphs of girth at least `6` have no induced `C₄` or `C₅`, and such a graph with
`K = 3` is an instance of the problem here. Golovach, Johnson, Paulusma, and Song, Theorem 21 (i) 1,
record the consequence: COLOURING is NP-complete for `(H₁, H₂)`-free graphs whenever `H₁ ⊇ᵢ C_r`
and `H₂ ⊇ᵢ C_s` with `r, s ≥ 3`. Membership in NP is immediate (a coloring is a certificate).

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable i.2.2`). The
restriction adds `0 < K ≤ |V|` (the bound of Garey and Johnson's [GT4]) and the two forbidden
induced cycles, Mathlib's `SimpleGraph.cycleGraph 4` and `SimpleGraph.cycleGraph 5` with
`SimpleGraph.IsIndContained` (an embedding that preserves adjacency and non-adjacency), as in
`ChordalBipartiteHamiltonianCircuitWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with
`0 < K ≤ |V|` whose graph has no induced `C₄` and no induced `C₅`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (0 < i.2.2 ∧ i.2.2 ≤ i.1) ∧
    ¬ (SimpleGraph.cycleGraph 4).IsIndContained (Graph i) ∧
    ¬ (SimpleGraph.cycleGraph 5).IsIndContained (Graph i)

open Classical in
/-- GRAPH K-COLORABILITY ON (C₄, C₅)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def graphColoringCFourCFiveFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **GRAPH K-COLORABILITY ON (C₄, C₅)-FREE GRAPHS is NP-complete.** Source: Garey and Johnson
(1979), [GT4]; Král', Kratochvíl, Tuza, and Woeginger (2001); Kamiński and Lozin (2007);
Golovach, Johnson, Paulusma, and Song (2017), Theorem 21 (i) 1. -/
public theorem_wanted graphColoringCFourCFiveFree_npComplete :
    graphColoringCFourCFiveFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphColoringCFourCFiveFreeDec

end MetaMathlibExt.Complexity.NPComplete.GraphColoringCFourCFiveFree

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER OF H-FREE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticNumberHFreeGraphs

/-!
# CHROMATIC NUMBER OF H-FREE GRAPHS is NP-complete

Fix a graph `H` that is not an induced subgraph of `P₄` or of `P₁ + P₃`.
INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) with no induced subgraph
isomorphic to `H`, and a positive integer `K`.
QUESTION: is `G` properly `K`-colorable?

This is GRAPH COLORING (`WantedExt.Complexity.NPComplete.GraphColoringWanted`) restricted to
`H`-free graphs. Král', Kratochvíl, Tuza and Woeginger show that for a fixed graph `H` it is
polynomial-time solvable if `H` is an induced subgraph of `P₄` or of `P₁ + P₃`, and
NP-complete otherwise; the theorem below states the NP-complete side, for every such `H`. The
instance type, the graph, the parent well-formedness condition and the question are those of
the parent module (`GraphColoring.GraphColoringInstance`, `GraphColoring.Graph`,
`GraphColoring.WellFormed`, `GraphColoring.GraphColoringFeasible`); `WellFormed` adds `0 < K`
and the `H`-freeness of the graph. `H` is any graph on
`Fin h`; induced subgraphs are Mathlib's `SimpleGraph.IsIndContained` (an embedding that
preserves adjacency and non-adjacency), `Pₘ` is `SimpleGraph.pathGraph m`, and `P₁ + P₃` is the
disjoint union `SimpleGraph.pathGraph 1 ⊕g SimpleGraph.pathGraph 3`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the forbidden graph `H`: it is a well-formed GRAPH
COLORING instance (a simple graph given by an edge list), `K` is positive, and `H` is not an
induced subgraph of its graph. -/
def WellFormed {h : ℕ} (H : SimpleGraph (Fin h)) (i : GraphColoring.GraphColoringInstance) :
    Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ ¬ H.IsIndContained (GraphColoring.Graph i)

open Classical in
/-- CHROMATIC NUMBER OF `H`-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def chromaticNumberHFreeGraphsDec {h : ℕ} (H : SimpleGraph (Fin h)) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed H i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **CHROMATIC NUMBER OF `H`-FREE GRAPHS is NP-complete** for every graph `H` that is not an
induced subgraph of `P₄` or of `P₁ + P₃`. Source: Garey and Johnson (1979), [GT4]; Král',
Kratochvíl, Tuza and Woeginger (2001). -/
public theorem_wanted chromaticNumberHFreeGraphs_npComplete {h : ℕ} (H : SimpleGraph (Fin h))
    (hP₄ : ¬ H.IsIndContained (SimpleGraph.pathGraph 4))
    (hP₁P₃ : ¬ H.IsIndContained (SimpleGraph.pathGraph 1 ⊕g SimpleGraph.pathGraph 3)) :
    chromaticNumberHFreeGraphsDec H ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (chromaticNumberHFreeGraphsDec H)

end MetaMathlibExt.Complexity.NPComplete.ChromaticNumberHFreeGraphs

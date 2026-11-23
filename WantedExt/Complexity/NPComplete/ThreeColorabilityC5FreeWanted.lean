/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF C5-FREE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY, the problem
restricted here;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
T. Emden-Weinert, S. Hougardy and B. Kreuter, "Uniquely colourable graphs and the hardness of
colouring graphs of large girth", Combinatorics, Probability and Computing 7 (1998), 375-386,
doi:10.1017/S0963548398003678.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ChromaticNumberHFreeGraphsWanted
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityC5Free

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance)

/-!
# 3-COLORABILITY OF C5-FREE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with no induced subgraph isomorphic to
the cycle `C_5` on 5 vertices.
QUESTION: is `G` 3-colorable, i.e. is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)` for
every edge `uv`?

This is GRAPH K-COLORABILITY (Garey and Johnson [GT4]) with `K = 3`, restricted to the class of
`C_5`-free graphs (ISGCI class `gc_359`). It is the case `H = C_5`, `K = 3` of CHROMATIC NUMBER
OF H-FREE GRAPHS (`ChromaticNumberHFreeGraphsWanted`), whose instance type, graph,
well-formedness and question are reused: a vertex count, an edge list on `Fin n` and a bound
`K` (`GraphColoring.GraphColoringInstance`, `GraphColoring.Graph`), the well-formedness
`ChromaticNumberHFreeGraphs.WellFormed (SimpleGraph.cycleGraph 5)` (a simple edge list,
`0 < K`, and no induced `C_5`), and the question `GraphColoring.GraphColoringFeasible`
(`(Graph i).Colorable K`). The restriction adds `K = 3`. A graph is `C_5`-free when Mathlib's
`(SimpleGraph.cycleGraph 5).IsIndContained G` (an embedding of `C_5` into `G` that preserves
adjacency and non-adjacency) fails.

Král', Kratochvíl, Tuza and Woeginger prove that 3-COLORABILITY is NP-complete for graphs of girth
at least `g`, for every fixed `g ≥ 3`, in order to show that coloring `H`-free graphs is NP-complete
whenever `H` contains a cycle; Emden-Weinert, Hougardy and Kreuter had proved the same for every
`K ≥ 3` and `g ≥ 3`, even with bounded maximum degree. A graph of girth at least 6 has no cycle of
length 5 at all, so it is `C_5`-free. Their reductions map each source instance to a graph of girth
at least 6, preserving the answer; since such a graph is `C_5`-free, the same reductions map into
this problem and prove it NP-hard. Membership in NP is immediate (a coloring is a certificate).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed CHROMATIC NUMBER OF H-FREE GRAPHS instance for
`H = C_5` (a simple edge list, a positive bound, and no induced `C_5` in the graph) whose bound
is `K = 3`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  ChromaticNumberHFreeGraphs.WellFormed (SimpleGraph.cycleGraph 5) i ∧ i.2.2 = 3

open Classical in
/-- 3-COLORABILITY OF C5-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityC5FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **3-COLORABILITY OF C5-FREE GRAPHS is NP-complete.** Source: Garey and Johnson (1979),
[GT4]; Král', Kratochvíl, Tuza and Woeginger (2001); Emden-Weinert, Hougardy and Kreuter
(1998). -/
public theorem_wanted threeColorabilityC5Free_npComplete :
    threeColorabilityC5FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityC5FreeDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityC5Free

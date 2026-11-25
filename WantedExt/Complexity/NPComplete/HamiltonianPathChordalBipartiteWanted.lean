/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on chordal bipartite graphs is NP-complete

Source:
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4 ("The main result of this paper is the
NP-completeness of the HAMILTONIAN CIRCUIT problem for chordal bipartite graphs. ... On both
classes the complexity of the HAMILTONIAN PATH problem coincides with the complexity of
HAMILTONIAN CIRCUIT");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathChordalBipartite

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance Graph)

/-!
# HAMILTONIAN PATH on chordal bipartite graphs is NP-complete

INSTANCE: a finite simple undirected chordal bipartite graph `G = (V, E)`: bipartite, with no
induced cycle of length at least `6` (ISGCI class `gc_79`).
QUESTION: does `G` contain a Hamiltonian path, i.e. a simple path through every vertex (endpoints
not specified)?

This is HAMILTONIAN PATH (Garey and Johnson [GT39]) restricted to chordal bipartite graphs; Müller
(1996) proves HAMILTONIAN CIRCUIT NP-complete there and states that HAMILTONIAN PATH has the same
complexity on the class. The instance type, the graph, the parent well-formedness condition and the
question are those of `HamiltonianPathUndirectedWanted` (`HamiltonianPathUndirectedInstance`: vertex
count and edge list on `Fin n`; `Graph`; `HamiltonianPathUndirected.WellFormed`: `0 < n` and a
simple edge list; `HamiltonianPathUndirected.HamiltonianPathUndirectedFeasible`: a list of all
vertices without repetition whose consecutive entries are adjacent), reused unchanged; `WellFormed`
adds the class conditions. Chordal bipartite is stated as in the merged
`ChordalBipartiteHamiltonianCircuitWanted`: Mathlib's `SimpleGraph.IsBipartite` and, for every
`k ≥ 6`, the cycle `SimpleGraph.cycleGraph k` is not an induced subgraph
(`SimpleGraph.IsIndContained`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance (`0 < n`, a simple
graph given by an edge list) that is bipartite and has no induced cycle of length at least `6`. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ (Graph i).IsBipartite ∧
    ∀ k, 6 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained (Graph i)

open Classical in
/-- HAMILTONIAN PATH on chordal bipartite graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathChordalBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧
      HamiltonianPathUndirected.HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH on chordal bipartite graphs is NP-complete.** Source: Müller (1996). -/
public theorem_wanted hamiltonianPathChordalBipartite_npComplete :
    hamiltonianPathChordalBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathChordalBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathChordalBipartite

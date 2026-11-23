/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on strongly chordal split graphs is NP-complete

Source:
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCircuitSplitGraphsWanted
public import WantedExt.Complexity.NPComplete.StronglyChordalSplitHamiltonianPathWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitStronglyChordalSplit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on strongly chordal split graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is both a split graph (its vertex set can be partitioned
into a clique and an independent set) and strongly chordal (every cycle of length at least `4`
has a chord, and every cycle of even length at least `6` has an odd chord, an edge joining two
vertices of the cycle at odd distance greater than `1` along the cycle).

QUESTION: does `G` contain a Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT ([GT37]) restricted to strongly chordal split graphs. Müller (1996,
abstract): "The main result of this paper is the NP-completeness of the HAMILTONIAN CIRCUIT
problem for chordal bipartite graphs. [...] As a corollary, HAMILTONIAN CIRCUIT is NP-complete
for strongly chordal split graphs." The ISGCI database lists HAMILTONIAN CYCLE as NP-complete on
the class "split ∩ strongly chordal" (gc_315), citing Müller.

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted` ([GT37]: a simple graph on
`Fin n` given by an edge list; a Hamiltonian circuit needs at least three vertices). The
restriction conjoins the two class predicates already used for this class by
`StronglyChordalSplitHamiltonianPathWanted` (HAMILTONIAN PATH on the same class):
* the split-graph condition, as `HamiltonianCircuitSplitGraphs.WellFormed` of
  `HamiltonianCircuitSplitGraphsWanted` (the HAMILTONIAN CIRCUIT instance conditions plus
  `DominatingSetSplitGraphs.IsSplitGraph`: a vertex set that is a clique, Mathlib's
  `SimpleGraph.IsClique`, whose complement is independent, `SimpleGraph.IsIndepSet`);
* strong chordality, `StronglyChordalSplitHamiltonianPath.IsStronglyChordal` (Brandstädt, Le and
  Spinrad, *Graph Classes: A Survey*, Definition 3.4.1: no induced cycle graph `Cₖ` with
  `k ≥ 4`, and every cycle of even length at least `6`, a closed walk with Mathlib's
  `SimpleGraph.Walk.IsCycle`, has an odd chord).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance on split graphs
(`HamiltonianCircuitSplitGraphs.WellFormed`) whose graph is strongly chordal. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCircuitSplitGraphs.WellFormed i ∧
    StronglyChordalSplitHamiltonianPath.IsStronglyChordal (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT on strongly chordal split graphs as a decision problem over
bitstrings. -/
noncomputable def hamiltonianCircuitStronglyChordalSplitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on strongly chordal split graphs is NP-complete.** Source: Müller
(1996); Garey and Johnson (1979), [GT37]. -/
public theorem_wanted hamiltonianCircuitStronglyChordalSplit_npComplete :
    hamiltonianCircuitStronglyChordalSplitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitStronglyChordalSplitDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitStronglyChordalSplit

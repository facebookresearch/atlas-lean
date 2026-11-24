/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on strongly chordal graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4 (NP-complete already for strongly chordal split graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted
public import WantedExt.Complexity.NPComplete.StronglyChordalSplitHamiltonianPathWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitStronglyChordal

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on strongly chordal graphs is NP-complete

INSTANCE: a strongly chordal graph `G = (V, E)`, i.e. a chordal graph in which every cycle of even
length at least `6` has an odd chord (an edge joining two vertices of the cycle at odd distance
greater than `1` along the cycle).
QUESTION: does `G` contain a Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT ([GT37]) restricted to strongly chordal graphs. Müller (1996,
abstract) proves HAMILTONIAN CIRCUIT NP-complete for chordal bipartite graphs and, as a
corollary, for strongly chordal split graphs; every strongly chordal split graph is strongly
chordal, so the problem is NP-complete on strongly chordal graphs.

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted` ([GT37]: a simple graph on
`Fin n` given by an edge list; a Hamiltonian circuit needs at least three vertices), as in
`ChordalBipartiteHamiltonianCircuitWanted`. The restriction adds the strong-chordality predicate
`StronglyChordalSplitHamiltonianPath.IsStronglyChordal` of
`StronglyChordalSplitHamiltonianPathWanted` (Brandstädt, Le and Spinrad, *Graph Classes: A
Survey*, Definition 3.4.1: no induced cycle graph `Cₖ` with `k ≥ 4`, and every cycle of even
length at least `6`, a closed walk with Mathlib's `SimpleGraph.Walk.IsCycle`, has an odd chord).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is
strongly chordal. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧
    StronglyChordalSplitHamiltonianPath.IsStronglyChordal (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT on strongly chordal graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitStronglyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on strongly chordal graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT37]; Müller (1996). -/
public theorem_wanted hamiltonianCircuitStronglyChordal_npComplete :
    hamiltonianCircuitStronglyChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitStronglyChordalDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitStronglyChordal

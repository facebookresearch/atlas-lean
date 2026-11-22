/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH on Hamiltonian graphs is NP-complete

Source:
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 7.3;
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024 (the
parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "hamiltonian"
(gc_1092), problem treewidth: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import WantedExt.Complexity.NPComplete.TreewidthWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthHamiltonian

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-!
# TREEWIDTH on Hamiltonian graphs is NP-complete

INSTANCE: a Hamiltonian graph `G = (V, E)` (one with a cycle through every vertex) and an
integer `K`. QUESTION: is the treewidth of `G` at most `K`?

Cavallaro, Theorem 7.3: "Treewidth is NP-complete on Hamiltonian graphs with known
Hamilton-cycle", where Treewidth asks, "given a graph `G` and some integer `k`, [...] whether
there is tree-decomposition of `G` with width `k`" (Section 7: "we will write `tw(G) ≤ k` if `G`
has treewidth at most `k`"), and "`G` is called Hamiltonian, if there is a cycle `C` with
`V(C) = V(G)`". The reduction, from TREEWIDTH on general graphs (Arnborg, Corneil and
Proskurowski), outputs a Hamiltonian cycle together with the graph; dropping the cycle gives a
reduction to the problem stated here, where the cycle is not part of the instance.

This is TREEWIDTH (`WantedExt.Complexity.NPComplete.TreewidthWanted`) restricted to Hamiltonian
graphs: the instance type, graph, well-formedness and question (`Treewidth.TreewidthFeasible`,
some tree decomposition with all bags of at most `K + 1` vertices) are those of that module, and
the restriction is added to well-formedness. It asks for a closed walk that is a Hamiltonian
cycle in Mathlib's sense (`SimpleGraph.Walk.IsHamiltonianCycle`: a cycle visiting every vertex
exactly once). Mathlib's `SimpleGraph.IsHamiltonian` would also hold, vacuously, for the
one-vertex graph, which has no cycle; the existence of a Hamiltonian cycle is stated directly so
that the class is the source's on every vertex count. A Hamiltonian cycle has `n` edges, so
`n ≤ |E|` and the binary vertex count does not make the encoding succinct. Membership in NP
takes a tree decomposition with at most `n` nodes and a Hamiltonian cycle as the certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (a simple edge list on
`Fin n`) whose graph has a Hamiltonian cycle. -/
def HamiltonianWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ ∃ (a : Fin i.1) (p : (Graph i).Walk a a), p.IsHamiltonianCycle

open Classical in
/-- TREEWIDTH on Hamiltonian graphs as a decision problem over bitstrings. -/
noncomputable def treewidthHamiltonianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (HamiltonianWellFormed i ∧ TreewidthFeasible i)
  | none => false

/-- **TREEWIDTH on Hamiltonian graphs is NP-complete.** Source: Cavallaro (2019), Theorem 7.3;
Arnborg, Corneil and Proskurowski (1987) (parent problem). -/
public theorem_wanted treewidthHamiltonian_npComplete :
    treewidthHamiltonianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treewidthHamiltonianDec

end MetaMathlibExt.Complexity.NPComplete.TreewidthHamiltonian

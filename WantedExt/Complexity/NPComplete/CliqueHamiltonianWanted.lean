/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on Hamiltonian graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE (the parent problem);
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 6.2 and Lemma 6.3;
ISGCI, *Information System on Graph Classes and their Inclusions*, class "hamiltonian"
(gc_1092), problem Clique: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueHamiltonian

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# CLIQUE on Hamiltonian graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is Hamiltonian (has a simple cycle
through every vertex), and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a clique of size `K` or more, that is, a subset `V' ⊆ V` with
`|V'| ≥ K` such that every two vertices of `V'` are joined by an edge in `E`?

This is CLIQUE ([GT19]) restricted to Hamiltonian graphs (ISGCI: "A graph is hamiltonian if it
has a simple cycle that goes through all vertices of the graph"). The instance type (vertex
count `n`, edge list, bound `K`), the graph (`GraphColoring.Graph`, the edge-list graph on
`Fin n`) and the simple-edge-list condition (`GraphColoring.WellFormed`) are reused from
`GraphColoringWanted`. The question is that of the edge-list CLIQUE statements on `main`
(`CliqueClawFreeWanted`, `CliqueBOneVPGWanted`): a `Finset` of at least `K` vertices whose
coercion is Mathlib's `SimpleGraph.IsClique`. Well-formedness adds `0 < K ≤ |V|` ([GT19]'s
instance class) and Hamiltonicity: at least 3 vertices and Mathlib's `SimpleGraph.IsHamiltonian`
(a Hamiltonian cycle exists), as in `HamiltonianCycleUndirectedWanted`; the bound excludes the
one-vertex graph, which Mathlib counts as Hamiltonian although it has no simple cycle.
The Hamiltonian cycle is not part of the instance; membership in NP takes the clique together
with a Hamiltonian cycle as the certificate.

Cavallaro's thesis proves Theorem 6.2, "Clique on Hamiltonian graphs with known Hamilton cycle
is NP-complete", by a reduction from CLIQUE: the Hamiltonian closure of `G` (Definition 4.2)
adds, for consecutive vertices `vᵢ, vᵢ₊₁` of an enumeration of `V` (cyclically), a new vertex
adjacent to exactly those two; it is Hamiltonian, and its cliques of four or more vertices are
exactly those of `G`, since the new vertices have degree 2 (Lemma 6.3; cliques of at most three
vertices are found by brute force). The reduction produces Hamiltonian graphs, so it also
reduces to this problem, whose instances omit the cycle.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `0 < K ≤ n`, and the
graph is Hamiltonian (`n ≥ 3` and a Hamiltonian cycle exists). -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ 3 ≤ i.1 ∧ (Graph i).IsHamiltonian

/-- The graph has a clique of size `K` or more. -/
def CliqueHamiltonianFeasible (i : GraphColoringInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1))

open Classical in
/-- CLIQUE on Hamiltonian graphs as a decision problem over bitstrings. -/
noncomputable def cliqueHamiltonianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ CliqueHamiltonianFeasible i)
  | none => false

/-- **CLIQUE on Hamiltonian graphs is NP-complete.** Source: Cavallaro (2019), Theorem 6.2;
Garey and Johnson (1979), [GT19] (parent problem). -/
public theorem_wanted cliqueHamiltonian_npComplete :
    cliqueHamiltonianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueHamiltonianDec

end MetaMathlibExt.Complexity.NPComplete.CliqueHamiltonian

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on locally connected graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE (the parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_932` (locally
connected), problem Clique: NP-complete, reference `ref_1506` (ISGCI note: adding a universal
vertex to a connected graph yields a locally connected graph and raises the size of a largest
clique by exactly one; communicated by P. Irzhavski). No published proof was found.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CliqueClawFreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueLocallyConnected

open CliqueClawFree (CliqueClawFreeInstance Graph CliqueClawFreeFeasible)

/-!
# CLIQUE on locally connected graphs is NP-complete

INSTANCE: a locally connected graph `G = (V, E)`, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a clique of size `K` or more, that is, a subset `V' ⊆ V` with
`|V'| ≥ K` such that every two vertices of `V'` are joined by an edge in `E`?

This is CLIQUE ([GT19]) on the ISGCI class `gc_932`. ISGCI's definition: "A graph G is locally
connected iff for every vertex v, the open neighbourhood N(v) of v induces a connected graph in
G." Here that is `∀ v, (G.induce (G.neighborSet v)).Connected`, as in
`LocallyConnectedHamiltonianCircuitWanted`. Mathlib's `SimpleGraph.Connected` includes
nonemptiness, so a graph with an isolated vertex is not locally connected here; the definition
does not say whether an empty neighbourhood induces a connected graph, and the reduction below
produces no isolated vertex, so hardness holds under either reading.

The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at least `K`
vertices whose coercion is Mathlib's `SimpleGraph.IsClique`) are those of the edge-list CLIQUE
statement on `main`, `WantedExt.Complexity.NPComplete.CliqueClawFreeWanted`, whose claw-free
restriction lives only in its `WellFormed`, which this module does not use. `WellFormed` here
asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT19]'s instance class), and the class.

Reduction from CLIQUE on connected graphs (ISGCI note `ref_1506`): for a connected graph `G`
with at least one vertex, adding a vertex `u` adjacent to all others gives a locally connected
graph (`N(u)` induces `G`, and every other `N(v)` contains `u`, which is adjacent to the rest of
`N(v)`), whose largest clique is one larger than that of `G`. The clique is a polynomial
certificate and local connectivity is checkable in polynomial time, so the problem is in NP.

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
duplicate edges in either orientation, no self-loops, endpoints in range) that is locally
connected (the neighbourhood of every vertex induces a connected graph), and `0 < K ≤ |V|`. -/
def WellFormed (i : CliqueClawFreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ v, ((Graph i).induce ((Graph i).neighborSet v)).Connected) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CLIQUE on locally connected graphs as a decision problem over bitstrings. -/
noncomputable def cliqueLocallyConnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueClawFreeInstance) x with
  | some i => decide (WellFormed i ∧ CliqueClawFreeFeasible i)
  | none => false

/-- **CLIQUE on locally connected graphs is NP-complete.** Source: ISGCI (`gc_932`, note
`ref_1506`); Garey and Johnson (1979), [GT19] (parent problem). -/
public theorem_wanted cliqueLocallyConnected_npComplete :
    cliqueLocallyConnectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueLocallyConnectedDec

end MetaMathlibExt.Complexity.NPComplete.CliqueLocallyConnected

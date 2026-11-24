/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on dually chordal graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET (the parent
problem);
A. Brandstädt, V. D. Chepoi and F. F. Dragan, "The algorithmic use of hypertree structure and
maximum neighbourhood orderings", Discrete Applied Mathematics 82(1-3) (1998), 43-77,
doi:10.1016/s0166-218x(97)00125-x (cited by ISGCI and Wikipedia for this result);
A. Brandstädt, F. F. Dragan, V. D. Chepoi and V. I. Voloshin, "Dually chordal graphs", SIAM
Journal on Discrete Mathematics 11(3) (1998), 437-455, doi:10.1137/S0895480193253415 (the
class);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_185` (dually
chordal), problem Independent set: NP-complete (Brandstädt, Chepoi and Dragan 1998).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Logic.Equiv.Defs
public import WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetDuallyChordal

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-!
# INDEPENDENT SET on dually chordal graphs is NP-complete

INSTANCE: a dually chordal graph `G = (V, E)`, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) on the ISGCI class `gc_185`. ISGCI's definition: "A vertex `u`
in `N[v]` is a maximum neighbour of `v` if for all `w` in `N[v]`: `N[w] ⊆ N[u]`. A vertex
ordering `v_1 … v_n` is a maximum neighbourhood ordering if for each `i < n` `v_i` has a maximum
neighbour in `G_i`. A graph is dually chordal if it has a maximum neighbourhood ordering." Here
`N[v]` is the closed neighbourhood and `G_i` is the subgraph induced by `v_i, …, v_n`.
`DuallyChordal` is this definition. (Brandstädt, Dragan, Chepoi and Voloshin state their results
for connected graphs; the hardness argument below produces connected graphs, so the theorem
covers that reading too.)

`IsMaximumNeighbourhoodOrdering G σ` states the ordering condition with `v_i = σ i` (positions
`Fin n`): every `σ i` has a vertex `σ j`, `i ≤ j`, in its closed neighbourhood in `G_i` whose
closed neighbourhood in `G_i` contains the closed neighbourhood in `G_i` of every `σ k` in the
closed neighbourhood of `σ i` in `G_i`. The condition for the last position holds trivially
(take `j = i`), so quantifying over all positions is ISGCI's "for each `i < n`".

The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at least `K`
vertices whose coercion is Mathlib's `SimpleGraph.IsIndepSet`) are those of the edge-list
INDEPENDENT SET statement on `main`,
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`, whose triangle-free
restriction lives only in its `WellFormed`, which this module does not use. `WellFormed` here
asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT20]'s instance class), and the class.

Reduction from INDEPENDENT SET: adding a vertex adjacent to all others yields a (connected)
dually chordal graph (any ordering that puts the new vertex last is a maximum neighbourhood
ordering, the new vertex being a maximum neighbour of every vertex), and for `K ≥ 2` it leaves
the independent sets of size `K` unchanged. ISGCI and Wikipedia ("Dually chordal graph",
Complexity of problems) record INDEPENDENT SET as NP-complete on dually chordal graphs, citing
Brandstädt, Chepoi and Dragan (1998).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The ordering `σ 0, σ 1, …, σ (n - 1)` of the vertices of `G` is a maximum neighbourhood
ordering: for every position `i`, with `G_i` the subgraph induced by the vertices at positions
`≥ i`, the vertex `σ i` has a maximum neighbour `σ j` in `G_i`, i.e. `σ j` lies in the closed
neighbourhood of `σ i` in `G_i`, and for every `σ k` in that closed neighbourhood, every `σ l`
in the closed neighbourhood of `σ k` in `G_i` lies in the closed neighbourhood of `σ j` in
`G_i`. -/
def IsMaximumNeighbourhoodOrdering {n : ℕ} (G : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, ∃ j, i ≤ j ∧ (j = i ∨ G.Adj (σ i) (σ j)) ∧
    ∀ k, i ≤ k → (k = i ∨ G.Adj (σ i) (σ k)) →
      ∀ l, i ≤ l → (l = k ∨ G.Adj (σ k) (σ l)) → (l = j ∨ G.Adj (σ j) (σ l))

/-- A graph is dually chordal if it has a maximum neighbourhood ordering. -/
def DuallyChordal {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ σ, IsMaximumNeighbourhoodOrdering G σ

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) that is dually
chordal, and `0 < K ≤ |V|`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    DuallyChordal (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on dually chordal graphs as a decision problem over bitstrings. -/
noncomputable def independentSetDuallyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

/-- **INDEPENDENT SET on dually chordal graphs is NP-complete.** Source: Brandstädt, Chepoi and
Dragan (1998); ISGCI (`gc_185`); Garey and Johnson (1979), [GT20] (parent problem). -/
public theorem_wanted independentSetDuallyChordal_npComplete :
    independentSetDuallyChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetDuallyChordalDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetDuallyChordal

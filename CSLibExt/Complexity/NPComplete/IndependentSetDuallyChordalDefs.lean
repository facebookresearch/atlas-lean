/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on dually chordal graphs: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Logic.Equiv.Defs
public import CSLibExt.Complexity.NPComplete.TriangleFreeIndependentSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetDuallyChordal

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.IndependentSetDuallyChordal

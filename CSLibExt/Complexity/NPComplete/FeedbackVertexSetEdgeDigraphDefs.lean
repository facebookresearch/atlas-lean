/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on edge digraphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET, comment on
p. 192 ("for edge digraphs [Gavril, 1977a]");
F. Gavril, "Some NP-complete problems on graphs", Proc. 11th Conference on Information Sciences
and Systems, Johns Hopkins University, Baltimore, MD (1977), 91-95;
F. Harary and R. Z. Norman, "Some properties of line digraphs", Rendiconti del Circolo
Matematico di Palermo 9 (1960), 161-168, doi:10.1007/BF02854581 (edge digraphs).
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Dichromatic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraph

/-- An instance: the number `n` of vertices (vertices `0, ..., n - 1`), the arc list `A` (arc
`(u, v)` from `u` to `v`), and the bound `K`. -/
abbrev FeedbackVertexSetEdgeDigraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The arc relation of an instance on its vertices `Fin n`. -/
def Arc (i : FeedbackVertexSetEdgeDigraphInstance) (u v : Fin i.1) : Prop :=
  ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- The digraph on `Fin n` with arc list `A` is an edge digraph: it is the line digraph of a
directed graph on `Fin m` without multiple arcs, vertex `a` being the arc `(tail a, head a)`. -/
def IsEdgeDigraph (n : ℕ) (A : List (ℕ × ℕ)) : Prop :=
  ∃ (m : ℕ) (tail head : Fin n → Fin m),
    Function.Injective (fun a => (tail a, head a)) ∧
      ∀ a b : Fin n, ((a : ℕ), (b : ℕ)) ∈ A ↔ head a = tail b

/-- Well-formedness of an instance: the arcs are distinct pairs of distinct vertices `< n` (a
directed graph without loops or multiple arcs), the digraph is an edge digraph, and
`0 < K ≤ n`. -/
def WellFormed (i : FeedbackVertexSetEdgeDigraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    IsEdgeDigraph i.1 i.2.1 ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at most `K` vertices meets every directed cycle (closed directed walk of
positive length). -/
def FeedbackVertexSetEdgeDigraphFeasible (i : FeedbackVertexSetEdgeDigraphInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ∀ (m : ℕ) (f : Fin (m + 2) → Fin i.1),
      SimpleGraph.IsDirectedCycle (Arc i) m f → ∃ j, f j ∈ S

open Classical in
/-- FEEDBACK VERTEX SET on edge digraphs as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetEdgeDigraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetEdgeDigraphInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetEdgeDigraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraph

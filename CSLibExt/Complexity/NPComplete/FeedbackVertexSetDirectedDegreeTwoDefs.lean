/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET (digraphs with in- and out-degree at most 2): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET,
pp. 191-192 (comment: "Remains NP-complete for digraphs having no in- or out-degree exceeding
2, [...]", attributed to [Garey and Johnson, ——], unpublished);
T. Bai, Y. Cao and M. Xiao, "Feedback set problems on bounded-degree (planar) graphs",
arXiv:2605.11407 (2026), Corollary 3.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Dichromatic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetDirectedDegreeTwo

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), the arc list, and the bound `K`. -/
abbrev FeedbackVertexSetDirectedInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The arc list describes a digraph on `0, …, n - 1` without loops or multiple arcs: no arc is
listed twice, both endpoints of every arc are below `n`, and no arc joins a vertex to
itself. -/
def SimpleArcs (i : FeedbackVertexSetDirectedInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2

/-- Every vertex has in-degree at most `d` (at most `d` listed arcs end at it) and out-degree
at most `d` (at most `d` listed arcs start at it). -/
def DegreeAtMost (i : FeedbackVertexSetDirectedInstance) (d : ℕ) : Prop :=
  ∀ v < i.1, (i.2.1.filter fun a => a.2 = v).length ≤ d ∧
    (i.2.1.filter fun a => a.1 = v).length ≤ d

/-- The arc relation of the digraph on `Fin n`: `Arc i u v` when `(u, v)` is a listed arc. -/
def Arc (i : FeedbackVertexSetDirectedInstance) (u v : Fin i.1) : Prop :=
  ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the digraph has no loops or multiple arcs, every vertex has
in-degree and out-degree at most 2, and `0 < K ≤ |V|`. -/
def WellFormed (i : FeedbackVertexSetDirectedInstance) : Prop :=
  SimpleArcs i ∧ DegreeAtMost i 2 ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- A feedback vertex set of at most `K` vertices: a set `V'` of at most `K` vertices
containing at least one vertex of every directed cycle (closed directed walk of positive
length, `SimpleGraph.IsDirectedCycle`). -/
def FeedbackVertexSetDirectedFeasible (i : FeedbackVertexSetDirectedInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ∀ (m : ℕ) (f : Fin (m + 2) → Fin i.1), SimpleGraph.IsDirectedCycle (Arc i) m f →
      ∃ j, f j ∈ S

open Classical in
/-- FEEDBACK VERTEX SET on digraphs with in- and out-degree at most 2, as a decision problem
over bitstrings. -/
noncomputable def feedbackVertexSetDirectedDegreeTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetDirectedInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetDirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetDirectedDegreeTwo

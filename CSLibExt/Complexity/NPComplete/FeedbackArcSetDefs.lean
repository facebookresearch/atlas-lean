/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK ARC SET: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), FEEDBACK ARC SET; R. M.
Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet

/-- **Instances of FEEDBACK ARC SET.** An instance of FEEDBACK ARC SET is a triple $(n, E, K)$
consisting of a natural number $n$ (the number of vertices), a finite list $E$ of ordered pairs
of natural numbers (the arcs) and a natural number $K$ (the bound). -/
abbrev FeedbackArcSetInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- **Directed adjacency for FEEDBACK ARC SET.** For a list $E$ of ordered pairs of natural numbers
and natural numbers $u$ and $v$, the directed adjacency test returns true when the pair $(u, v)$
occurs in $E$, that is, when $E$ contains an arc from $u$ to $v$, and false otherwise. -/
def DAdj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v)


/-- **Well-formed FEEDBACK ARC SET instances.** An instance $(n, E, K)$ of FEEDBACK ARC SET is
well formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies
$u < n$, $v < n$ and $u \ne v$; that is, $E$ lists distinct arcs, without loops, of a directed
graph on the vertices $0, \dots, n-1$. -/
def WellFormed (i : FeedbackArcSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- **Feasible FEEDBACK ARC SET instances.** An instance $(n, E, K)$ of FEEDBACK ARC SET is
feasible when there is an ordering $v_0, v_1, \dots, v_{n-1}$ of the vertices $0, \dots, n-1$, in
which each of them occurs exactly once, such that at most $K$ entries $(u, v)$ of the list $E$,
counted with repetition, are backward, meaning that the position of $v$ in the ordering is
strictly smaller than the position of $u$. Here $v_j$ has position $j$, and a number that is not
among $0, \dots, n-1$ has position $n$. -/
def FeedbackArcSetFeasible
    (i : FeedbackArcSetInstance) : Prop :=
  ∃ ord : List ℕ, ord.Perm (List.range i.1) ∧
    (i.2.1.filter (fun e => decide (ord.idxOf e.2 < ord.idxOf e.1))).length ≤ i.2.2

open Classical in
/-- **FEEDBACK ARC SET as a decision problem.** The decision problem FEEDBACK ARC SET accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of instances, to
an instance $(n, E, K)$ of FEEDBACK ARC SET that is well formed and feasible. Bitstrings that do
not decode to an instance are rejected. -/
noncomputable def feedbackArcSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackArcSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackArcSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet

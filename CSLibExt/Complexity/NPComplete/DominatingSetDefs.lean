/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

/-!
# DOMINATING SET: definitions

The definitions that the statements of `WantedExt.Complexity.NPComplete.DominatingSetWanted`, and of
the wanted modules built on it, use, moved here unchanged so that their proofs can import them.

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), DOMINATING SET.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-- **Instances of DOMINATING SET.** An instance of DOMINATING SET is a triple $(n, E, K)$ of a
natural number $n$ (the number of vertices), a list $E$ of pairs of natural numbers (the edges)
and a natural number $K$ (the bound). -/
abbrev DominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of a DOMINATING SET instance.** For an instance $(n, E, K)$ of DOMINATING SET, its
graph is the simple graph on $\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are
adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. -/
def Graph (i : DominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- **Well-formed DOMINATING SET instances.** An instance $(n, E, K)$ of DOMINATING SET is well
formed when the list $E$ has no repeated entries and every pair $(u, v) \in E$ satisfies $u < n$,
$v < n$, $u \ne v$ and $(v, u) \notin E$. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasibility of a DOMINATING SET instance.** An instance $(n, E, K)$ of DOMINATING SET is
feasible when there is a set $S$ of at most $K$ vertices of its graph such that every vertex lies in
$S$ or is adjacent to a vertex of $S$, where the graph has vertex set $\{0, \dots, n - 1\}$ and
distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. -/
def DominatingSetFeasible
    (i : DominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ∀ v : Fin i.1, v ∈ S ∨ ∃ u ∈ S, (Graph i).Adj u v

open Classical in
/-- **DOMINATING SET as a decision problem.** The decision problem DOMINATING SET accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a triple
$(n, E, K)$ of a natural number $n$, a list $E$ of pairs of natural numbers and a natural number
$K$ such that $E$ has no repeated entries, every pair $(u, v) \in E$ satisfies $u < n$, $v < n$,
$u \ne v$ and $(v, u) \notin E$, and there is a set $S$ of at most $K$ vertices with every vertex
in $S$ or adjacent to a vertex of $S$, in the graph on $\{0, \dots, n - 1\}$ where distinct $i$
and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. Bitstrings that do not decode are
rejected. -/
noncomputable def dominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), INDEPENDENT DOMINATING
SET (a small maximal independent set).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSet

/-- **Independent dominating set instances.** An instance of INDEPENDENT DOMINATING SET is a
triple $(n, E, K)$ of a natural number $n$, the number of vertices, a list $E$ of pairs of
natural numbers, the edges, and a natural number $K$, the bound on the size of the set. -/
abbrev IndependentDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of an independent dominating set instance.** For an independent dominating set
instance with $n$ vertices and edge list $E$, the graph of the instance is the simple graph on
$\{0, \dots, n-1\}$ in which distinct vertices $u$ and $v$ are adjacent when $(u, v)$ or
$(v, u)$ belongs to $E$. -/
def Graph (i : IndependentDominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed independent dominating set instances.** An independent dominating set instance
$(n, E, K)$ is well formed when the list $E$ has no repeated entries and every pair $(a, b)$ in
$E$ satisfies $a < n$, $b < n$, $a \ne b$, and $(b, a)$ does not belong to $E$. -/
def WellFormed (i : IndependentDominatingSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Instances with a small independent dominating set.** An independent dominating set instance
$(n, E, K)$ has a small independent dominating set when there is a set $S$ of vertices of its
graph with at most $K$ elements such that every vertex lies in $S$ or is adjacent to a vertex of
$S$, and no two distinct vertices of $S$ are adjacent. -/
def IndependentDominatingSetFeasible
    (i : IndependentDominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    (∀ v : Fin i.1, v ∈ S ∨ ∃ u ∈ S, (Graph i).Adj u v) ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ (Graph i).Adj u v

open Classical in
/-- **INDEPENDENT DOMINATING SET as a decision problem.** The decision problem INDEPENDENT
DOMINATING SET accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to an independent dominating set instance $(n, E, K)$ that is well formed and whose
graph has an independent dominating set of at most $K$ vertices. It rejects every bitstring
that does not decode to an instance. -/
noncomputable def independentDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ IndependentDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSet

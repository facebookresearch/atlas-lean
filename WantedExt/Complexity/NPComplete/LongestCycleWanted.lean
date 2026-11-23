/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST CYCLE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LONGEST CYCLE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestCycle

/-!
# LONGEST CYCLE is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has a simple cycle with
at least `K` edges (and at least three vertices).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of LONGEST CYCLE.** An instance of LONGEST CYCLE is a triple $(n, E, K)$ of a
natural number $n$ (the number of vertices), a list $E$ of pairs of natural numbers (the edges),
and a natural number $K$ (the bound). -/
abbrev LongestCycleInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of a LONGEST CYCLE instance.** For an instance $(n, E, K)$ of LONGEST CYCLE, its graph
is the simple graph on $\{0, \dots, n-1\}$ in which distinct vertices $i$ and $j$ are adjacent
when $(i, j)$ or $(j, i)$ belongs to $E$. Loops are dropped, and pairs with an endpoint at least
$n$ contribute no edge. -/
def Graph (i : LongestCycleInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed LONGEST CYCLE instances.** An instance $(n, E, K)$ of LONGEST CYCLE is well
formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies
$u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$. -/
def WellFormed (i : LongestCycleInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible LONGEST CYCLE instances.** An instance $(n, E, K)$ of LONGEST CYCLE is feasible when
there are pairwise distinct vertices $v_1, \dots, v_m$ of the graph of the instance, with $m \ge K$
and $m \ge 3$, such that $v_j$ is adjacent to $v_{j+1}$ for every $1 \le j < m$ and $v_m$ is
adjacent to $v_1$. That is, the graph has a simple cycle with at least $K$ edges and at least
three vertices. -/
def LongestCycleFeasible
    (i : LongestCycleInstance) : Prop :=
  ∃ cycle : List (Fin i.1), cycle.Nodup ∧ i.2.2 ≤ cycle.length ∧ 3 ≤ cycle.length ∧
    (∀ j (h : j + 1 < cycle.length),
      (Graph i).Adj (cycle[j]'(by omega)) (cycle[j + 1]'h)) ∧
    ∀ h : cycle ≠ [], (Graph i).Adj (cycle.getLast h) (cycle.head h)

open Classical in
/-- **The decision problem LONGEST CYCLE.** LONGEST CYCLE accepts a bitstring $x$ exactly when $x$
decodes, under the canonical bitstring encoding of instances, to an instance of LONGEST CYCLE that
is well formed and feasible. Bitstrings that do not decode, and bitstrings that decode to
instances that are not well formed, are rejected. -/
noncomputable def longestCycleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestCycleInstance) x with
  | some i => decide (WellFormed i ∧ LongestCycleFeasible i)
  | none => false

/-- **LONGEST CYCLE is NP-complete.** The decision problem LONGEST CYCLE belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to LONGEST CYCLE.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), LONGEST CYCLE. -/
public theorem_wanted longestCycle_npComplete :
    longestCycleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestCycleDec

end MetaMathlibExt.Complexity.NPComplete.LongestCycle

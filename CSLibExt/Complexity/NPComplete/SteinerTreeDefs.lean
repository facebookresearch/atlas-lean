/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), STEINER TREE IN GRAPHS;
R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTree

/-- **Steiner tree instances.** A Steiner tree instance is a quadruple $(n, E, R, K)$ of a
natural number $n$ (the number of vertices), a list $E$ of triples $(u, v, w)$ of natural numbers
(an edge between $u$ and $v$ of weight $w$), a list $R$ of natural numbers (the terminals) and a
natural number $K$ (the budget). -/
abbrev SteinerTreeInstance := ℕ × List (ℕ × ℕ × ℕ) × List ℕ × ℕ


/-- **Graph of a candidate edge set.** Given a Steiner tree instance with vertex count $n$ and a
list $T$ of triples $(u, v, w)$ of natural numbers, the graph of $T$ is the simple graph on
$\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are adjacent when $(i, j, w)$ or
$(j, i, w)$ belongs to $T$ for some natural number $w$. Weights are ignored, and triples with an
endpoint at least $n$ contribute no edge. -/
def Graph (i : SteinerTreeInstance) (T : List (ℕ × ℕ × ℕ)) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (T.map fun e => (e.1, e.2.1))


/-- **Well-formed Steiner tree instances.** A Steiner tree instance with vertex count $n$, edge
list $E$ of triples $(u, v, w)$ and terminal list $R$ is well formed when $E$ has no repeated
entries; every $(u, v, w)$ in $E$ has $u < n$, $v < n$, $u \ne v$ and $w > 0$; any two entries
of $E$ with the same endpoints, in the same or the reverse order, are equal; $R$ has no repeated
entries; and every terminal in $R$ is less than $n$. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ 0 < e.2.2) ∧
    (∀ e1 ∈ i.2.1, ∀ e2 ∈ i.2.1,
      (e1.1 = e2.1 ∧ e1.2.1 = e2.2.1 ∨ e1.1 = e2.2.1 ∧ e1.2.1 = e2.1) → e1 = e2) ∧
    i.2.2.1.Nodup ∧ ∀ t ∈ i.2.2.1, t < i.1

/-- **Feasible Steiner tree instances.** A Steiner tree instance with vertex count $n$, edge list
$E$ of triples $(u, v, w)$, terminal list $R$ and budget $K$ is feasible when every terminal in
$R$ is less than $n$ and there is a sublist $T$ of $E$ (a not necessarily contiguous
subsequence) whose weights $w$ sum to at most $K$ such that any two terminals in $R$ are joined
by a path in the graph of $T$, the simple graph on $\{0, \dots, n - 1\}$ in which distinct
vertices are adjacent when they are the endpoints $u, v$ of some triple in $T$. -/
def SteinerTreeFeasible
    (i : SteinerTreeInstance) : Prop :=
  ∃ T : List (ℕ × ℕ × ℕ), T.Sublist i.2.1 ∧ (T.map (fun e => e.2.2)).sum ≤ i.2.2.2 ∧
    (∀ t ∈ i.2.2.1, t < i.1) ∧
    ∀ a ∈ i.2.2.1, ∀ ha : a < i.1, ∀ b ∈ i.2.2.1, ∀ hb : b < i.1,
      (Graph i T).Reachable ⟨a, ha⟩ ⟨b, hb⟩

open Classical in
/-- **The STEINER TREE decision problem.** The decision problem STEINER TREE accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding of Steiner tree instances,
to a Steiner tree instance that is both well formed and feasible. Bitstrings that do not decode
are rejected. -/
noncomputable def steinerTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerTree

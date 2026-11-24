/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LONGEST PATH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestPath

/-!
# LONGEST PATH is NP-complete

An undirected graph, a bound `K`, and distinguished endpoints `s` and `t` (Garey-Johnson ND29).
The question is whether the graph has a simple path from `s` to `t` with at least `K` edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Longest-path instances.** A longest-path instance is a tuple $(n, E, K, s, t)$ consisting of
a natural number $n$, the number of vertices; a list $E$ of pairs of natural numbers, the edges;
and natural numbers $K$, the length bound, $s$, the start vertex, and $t$, the target vertex. -/
abbrev LongestPathInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- **Graph of a longest-path instance.** For a longest-path instance with vertex count $n$ and
edge list $E$, its graph is the graph of the edge list $E$ on $n$ vertices: the simple graph on
$\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or
$(j, i)$ belongs to $E$. -/
def Graph (i : LongestPathInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed longest-path instances.** A longest-path instance $(n, E, K, s, t)$ is well
formed when $s < n$, $t < n$, the list $E$ has no repeated entries, and every pair $(u, v)$ in
$E$ satisfies $u < n$, $v < n$ and $u \ne v$, and its reverse $(v, u)$ does not belong to $E$. -/
def WellFormed (i : LongestPathInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.1 < i.1 ∧ i.2.2.2.2 < i.1

/-- **Feasibility of a longest-path instance.** A longest-path instance $(n, E, K, s, t)$ is
feasible when the graph of $E$ on $n$ vertices has a simple path from $s$ to $t$ with at least
$K$ edges, that is, a list $v_0, \dots, v_m$ of pairwise distinct vertices with $m \ge K$,
$v_0 = s$ and $v_m = t$, in which $v_j$ and $v_{j+1}$ are adjacent for every $j < m$. -/
def LongestPathFeasible
    (i : LongestPathInstance) : Prop :=
  ∃ path : List (Fin i.1), path.Nodup ∧ i.2.2.1 + 1 ≤ path.length ∧
    (path.head?.map fun v => (v : ℕ)) = some i.2.2.2.1 ∧
    (path.getLast?.map fun v => (v : ℕ)) = some i.2.2.2.2 ∧
    ∀ j (h : j + 1 < path.length),
      (Graph i).Adj (path[j]'(by omega)) (path[j + 1]'h)

open Classical in
/-- **The LONGEST PATH decision problem.** LONGEST PATH is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a longest-path
instance $(n, E, K, s, t)$ that is well formed and in which the graph of $E$ on $n$ vertices has
a simple path from $s$ to $t$ with at least $K$ edges. Bitstrings that do not decode to a
longest-path instance are rejected. -/
noncomputable def longestPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestPathInstance) x with
  | some i => decide (WellFormed i ∧ LongestPathFeasible i)
  | none => false

/-- **LONGEST PATH is NP-complete.** The LONGEST PATH decision problem belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to LONGEST PATH.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), LONGEST PATH. -/
public theorem_wanted longestPath_npComplete :
    longestPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestPathDec

end MetaMathlibExt.Complexity.NPComplete.LongestPath

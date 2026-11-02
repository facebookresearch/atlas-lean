/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIWAY CUT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MULTIWAY CUT; E. Dahlhaus
et al., "The complexity of multiterminal cuts" (1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiwayCut

/-!
# MULTIWAY CUT is NP-complete

An undirected graph, a list of terminals, and a bound `K`. The question is whether the
terminals can be pairwise separated by removing at most `K` edges, witnessed by an assignment
of every vertex to one terminal's part, sending each terminal to its own part, with at most `K`
cut edges, stated by forbidding `K + 1` cut edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Multiway cut instances.** A multiway cut instance is a tuple $(n, E, T, K)$ consisting of a
natural number $n$ (the number of vertices), a list $E$ of pairs of natural numbers (the edges), a
list $T$ of natural numbers (the terminals) and a natural number $K$ (the bound on the number of
cut edges). -/
abbrev MultiwayCutInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- **Well-formed multiway cut instances.** A multiway cut instance $(n, E, T, K)$ is well-formed
when the entries of $E$ are pairwise distinct; every entry $(u, v)$ of $E$ satisfies $u < n$,
$v < n$ and $u \ne v$, and $(v, u)$ is not an entry of $E$; the entries of $T$ are pairwise
distinct; and every entry $t$ of $T$ satisfies $t < n$. Thus $E$ lists each edge of a simple
undirected graph on the vertices $0, \dots, n-1$ exactly once, in one orientation, and $T$ is a
list of distinct vertices. No condition is imposed on $K$. -/
def WellFormed (i : MultiwayCutInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.Nodup ∧ ∀ t ∈ i.2.2.1, t < i.1

/-- **Feasible multiway cut instances.** Let $(n, E, T, K)$ be a multiway cut instance with
terminal list $T = (t_0, \dots, t_{k-1})$. It is feasible when there is a labelling $f$ of the
vertices $0, \dots, n-1$ by labels in $\{0, \dots, \max(k, 1) - 1\}$ such that $f(t_j) = j$ for
every $j < k$, and at most $K$ entries $(u, v)$ of $E$, counted with repetition, satisfy
$f(u) \ne f(v)$. Here every number $v \ge n$ counts as a vertex with label $0$. -/
def MultiwayCutFeasible
    (i : MultiwayCutInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1 ∧
    (∀ v < i.1, assign.getD v 0 < max i.2.2.1.length 1) ∧
    (∀ t < i.2.2.1.length, assign.getD (i.2.2.1.getD t 0) 0 = t) ∧
    ¬ ∃ cut : List (ℕ × ℕ), cut.Sublist i.2.1 ∧ cut.length = i.2.2.2 + 1 ∧
      ∀ e ∈ cut, assign.getD e.1 0 ≠ assign.getD e.2 0

open Classical in
/-- **The MULTIWAY CUT decision problem.** MULTIWAY CUT is the decision problem on bitstrings that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
multiway cut instance $(n, E, T, K)$ that is well-formed and feasible. Bitstrings that do not
decode to a multiway cut instance are rejected. -/
noncomputable def multiwayCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiwayCutInstance) x with
  | some i => decide (WellFormed i ∧ MultiwayCutFeasible i)
  | none => false

/-- **MULTIWAY CUT is NP-complete.** Let MULTIWAY CUT be the decision problem that accepts exactly
the bitstrings decoding to a well-formed, feasible multiway cut instance: a simple undirected graph
on the vertices $0, \dots, n-1$, a list of distinct terminal vertices and a bound $K$ such that
deleting at most $K$ edges of the graph leaves no two terminals connected. Then MULTIWAY CUT is in
NP, and every decision problem in NP reduces to MULTIWAY CUT by a polynomial-time many-one
reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), MULTIWAY CUT; E. Dahlhaus et al., "The complexity of multiterminal
cuts" (1994). -/
public theorem_wanted multiwayCut_npComplete :
    multiwayCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiwayCutDec

end MetaMathlibExt.Complexity.NPComplete.MultiwayCut

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BANDWIDTH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BANDWIDTH; C. H.
Papadimitriou, "The NP-completeness of the bandwidth minimization problem" (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Bandwidth

/-!
# BANDWIDTH is NP-complete

An undirected graph and a bound `K`. The question is whether the vertices can be labeled with
`0, …, n - 1` (a bijection) so that the endpoints of every edge receive labels differing by at
most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BANDWIDTH instances.** An instance of BANDWIDTH is a triple $(n, E, K)$ of a natural number
$n$ (the number of vertices), a list $E$ of ordered pairs of natural numbers (the edges) and a
natural number $K$ (the bound). -/
abbrev BandwidthInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed BANDWIDTH instances.** A BANDWIDTH instance $(n, E, K)$ is well formed when the
list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$ and
$u \ne v$, and its reverse $(v, u)$ does not occur in $E$. Thus $E$ lists the edges of a loopless
undirected graph on the vertices $0, \dots, n-1$, each edge exactly once. -/
def WellFormed (i : BandwidthInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **BANDWIDTH feasibility.** A BANDWIDTH instance $(n, E, K)$ is feasible when there is an
ordering of the numbers $0, \dots, n-1$ such that $|p(u) - p(v)| \le K$ for every pair $(u, v)$
in $E$, where $p(m)$ is the position of $m$ in the ordering, counting from $0$, and $p(m) = n$
when $m$ is not among $0, \dots, n-1$. -/
def BandwidthFeasible
    (i : BandwidthInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    ∀ e ∈ i.2.1, Nat.dist (perm.idxOf e.1) (perm.idxOf e.2) ≤ i.2.2

open Classical in
/-- **The BANDWIDTH decision problem.** BANDWIDTH accepts a bitstring $x$ exactly when $x$
decodes, under the canonical bitstring encoding of triples $(n, E, K)$ of a natural number, a
list of pairs of natural numbers and a natural number, to a BANDWIDTH instance that is both well
formed and feasible. Bitstrings that do not decode to such a triple are rejected. -/
noncomputable def bandwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BandwidthInstance) x with
  | some i => decide (WellFormed i ∧ BandwidthFeasible i)
  | none => false

/-- **BANDWIDTH is NP-complete.** The BANDWIDTH decision problem belongs to NP, and every decision
problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), BANDWIDTH; C. H. Papadimitriou, "The NP-completeness of the
bandwidth minimization problem" (1976). -/
public theorem_wanted bandwidth_npComplete :
    bandwidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bandwidthDec

end MetaMathlibExt.Complexity.NPComplete.Bandwidth

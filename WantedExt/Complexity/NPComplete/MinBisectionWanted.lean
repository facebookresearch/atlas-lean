/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BISECTION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM BISECTION.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinBisection

/-!
# MINIMUM BISECTION is NP-complete

An undirected graph with an even number of vertices and a bound `K`. The question is whether
the vertices can be split into two sets of exactly `n / 2` vertices each with at most `K` edges
crossing, stated by forbidding `K + 1` crossing edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of MINIMUM BISECTION.** An instance of MINIMUM BISECTION is a triple
$(n, es, K)$ of a natural number $n$ (the number of vertices), a list $es$ of pairs of natural
numbers (the edge list) and a natural number $K$ (the bound on the number of crossing edges). -/
abbrev MinBisectionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed MINIMUM BISECTION instances.** An instance $(n, es, K)$ of MINIMUM BISECTION is
well formed when $n$ is even, the list $es$ has no repeated entries, and every entry $(u, v)$ of
$es$ satisfies $u < n$, $v < n$ and $u \ne v$, and $(v, u)$ is not an entry of $es$. -/
def WellFormed (i : MinBisectionInstance) : Prop :=
  i.1 % 2 = 0 ∧ i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible MINIMUM BISECTION instances.** An instance $(n, es, K)$ of MINIMUM BISECTION is
feasible when there is a set $S \subseteq \{0, \dots, n - 1\}$ with $\lfloor n / 2 \rfloor$
elements such that no sublist of $es$ (a list obtained from $es$ by deleting entries) with
$K + 1$ entries consists only of entries $(u, v)$ with exactly one of $u$ and $v$ in $S$; that
is, at most $K$ entries of $es$ have exactly one endpoint in $S$. -/
def MinBisectionFeasible
    (i : MinBisectionInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧ S.card = i.1 / 2 ∧
    ¬ ∃ cut : List (ℕ × ℕ), cut.Sublist i.2.1 ∧ cut.length = i.2.2 + 1 ∧
      ∀ e ∈ cut, (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)

open Classical in
/-- **The decision problem MINIMUM BISECTION.** The decision problem MINIMUM BISECTION accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of instances, to an
instance $(n, es, K)$ of MINIMUM BISECTION that is well formed and feasible (its vertices split
into two sets of $n / 2$ vertices with at most $K$ entries of $es$ between them). Bitstrings that
do not decode are rejected. -/
noncomputable def minBisectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinBisectionInstance) x with
  | some i => decide (WellFormed i ∧ MinBisectionFeasible i)
  | none => false

/-- **MINIMUM BISECTION is NP-complete.** The decision problem MINIMUM BISECTION belongs to NP,
and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), MINIMUM BISECTION. -/
public theorem_wanted minBisection_npComplete :
    minBisectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minBisectionDec

end MetaMathlibExt.Complexity.NPComplete.MinBisection

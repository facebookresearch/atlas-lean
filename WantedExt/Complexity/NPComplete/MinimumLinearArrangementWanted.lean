/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM LINEAR ARRANGEMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM LINEAR
ARRANGEMENT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumLinearArrangement

/-!
# MINIMUM LINEAR ARRANGEMENT is NP-complete

An undirected graph and a bound `K`. The question is whether the vertices can be labeled with
`0, …, n - 1` (a bijection) so that the sum over edges of the label differences is at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Minimum linear arrangement instance.** An instance of MINIMUM LINEAR ARRANGEMENT is a triple
$(n, E, K)$ of a natural number $n$ (the number of vertices), a finite list $E$ of ordered pairs
of natural numbers (the edges) and a natural number $K$ (the bound). -/
abbrev MinimumLinearArrangementInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed minimum linear arrangement instance.** An instance $(n, E, K)$ of MINIMUM LINEAR
ARRANGEMENT is well formed when the list $E$ has no repeated entries and every pair $(u, v)$ in
$E$ satisfies $u < n$, $v < n$ and $u \ne v$, while the reversed pair $(v, u)$ does not occur in
$E$. Thus $E$ lists the edges of a simple graph on the vertices $0, \dots, n-1$, each edge once and
in one orientation. -/
def WellFormed (i : MinimumLinearArrangementInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible minimum linear arrangement instance.** An instance $(n, E, K)$ of MINIMUM LINEAR
ARRANGEMENT is feasible when there is an ordering $\pi$ of $0, 1, \dots, n-1$ (a list containing
each of these numbers exactly once) such that $\sum_{(u, v) \in E} |\pi(u) - \pi(v)| \le K$. Here
$\pi(v)$ is the position of $v$ in $\pi$, counted from $0$, and is $n$ when $v \ge n$; the sum
runs over the list $E$, so a repeated pair is counted once for each occurrence. -/
def MinimumLinearArrangementFeasible
    (i : MinimumLinearArrangementInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    (i.2.1.map (fun e => Nat.dist (perm.idxOf e.1) (perm.idxOf e.2))).sum ≤ i.2.2

open Classical in
/-- **The MINIMUM LINEAR ARRANGEMENT decision problem.** It accepts a bitstring $x$ exactly when
$x$ decodes, under the canonical bitstring encoding, to a triple $(n, E, K)$ of a natural number
$n$, a list $E$ of pairs of natural numbers and a natural number $K$ with the following
properties: every entry of $E$ is a pair $(u, v)$ of distinct numbers below $n$, the list $E$ has
no repeated entries and never contains both $(u, v)$ and $(v, u)$, and there is an ordering of
$0, 1, \dots, n-1$ in which, writing $p(v)$ for the position of $v$, the sum of $|p(u) - p(v)|$
over all pairs $(u, v)$ in $E$ is at most $K$. Bitstrings that do not decode are rejected. -/
noncomputable def minimumLinearArrangementDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ MinimumLinearArrangementFeasible i)
  | none => false

/-- **MINIMUM LINEAR ARRANGEMENT is NP-complete.** The MINIMUM LINEAR ARRANGEMENT decision problem
lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MINIMUM LINEAR ARRANGEMENT. -/
public theorem_wanted minimumLinearArrangement_npComplete :
    minimumLinearArrangementDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumLinearArrangementDec

end MetaMathlibExt.Complexity.NPComplete.MinimumLinearArrangement

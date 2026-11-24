/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LIST COLORING is NP-complete

Source:
J. Kratochvíl and Z. Tuza, "Algorithmic complexity of list colorings", Discrete Applied
Mathematics, 1994.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ListColoring

/-!
# LIST COLORING is NP-complete

An undirected graph with an explicit finite color list for every vertex. The question is
whether there is a proper coloring choosing each vertex's color from its own list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **List-coloring instances.** A list-coloring instance is a triple $(n, E, L)$ of a natural
number $n$ (the number of vertices), a list $E$ of pairs of natural numbers (the edges), and a
list $L$ of lists of natural numbers (the allowed colors of each vertex). -/
abbrev ListColoringInstance := ℕ × List (ℕ × ℕ) × List (List ℕ)

/-- **Well-formed list-coloring instances.** A list-coloring instance $(n, E, L)$ is well formed
when the edge list $E$ has no repeated entries, every edge $(u, v)$ in $E$ satisfies $u < n$,
$v < n$ and $u \ne v$ and its reversal $(v, u)$ does not occur in $E$, and the list $L$ of
color lists has length $n$. -/
def WellFormed (i : ListColoringInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.length = i.1

/-- **Feasible list-coloring instances.** A list-coloring instance $(n, E, L)$ is feasible when
there is a list $c = (c_0, \dots, c_{n-1})$ of $n$ natural numbers such that for every $v < n$
the number $c_v$ belongs to the $v$-th entry $L_v$ of $L$ (taken to be the empty list when $L$
has at most $v$ entries), and $c_u \ne c_v$ for every edge $(u, v)$ in $E$, where $c_w$ is read
as $0$ when $w \ge n$. -/
def ListColoringFeasible
    (i : ListColoringInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1 ∧
    (∀ v < i.1, assign.getD v 0 ∈ i.2.2.getD v []) ∧
    ∀ e ∈ i.2.1, assign.getD e.1 0 ≠ assign.getD e.2 0

open Classical in
/-- **The LIST COLORING decision problem.** LIST COLORING is the decision problem that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
list-coloring instance that is well formed and feasible. Bitstrings that do not decode are
rejected. -/
noncomputable def listColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ListColoringInstance) x with
  | some i => decide (WellFormed i ∧ ListColoringFeasible i)
  | none => false

/-- **LIST COLORING is NP-complete.** The LIST COLORING decision problem belongs to NP, and every
decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: J. Kratochvíl and Z. Tuza, "Algorithmic
complexity of list colorings", Discrete Applied Mathematics, 1994. -/
public theorem_wanted listColoring_npComplete :
    listColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L listColoringDec

end MetaMathlibExt.Complexity.NPComplete.ListColoring

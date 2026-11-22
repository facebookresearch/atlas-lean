/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-CENTER (GENERALIZED, NONMETRIC) is NP-complete

Source:
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KCenter

/-!
# k-CENTER (GENERALIZED, NONMETRIC) is NP-complete

Generalized, nonmetric k-center: client-to-location costs (an arbitrary rectangular matrix of
natural numbers, one row per client, no metric assumed, clients and facilities distinct sets),
a bound `K` on the number of open locations, and a radius `B`. The question is whether at most
`K` locations can be opened so that every client is within cost `B` of an open location. The
metric p-center problem of Kariv-Hakimi is the special case of a metric cost matrix; hardness
follows from that subclass (e.g. the dominating-set reduction with costs 1 on edges, 2 on
nonedges, 0 on the diagonal, radius 1).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **k-center instances.** An instance of generalized nonmetric k-center is a triple $(D, K, B)$
of a finite list $D$ of rows, each a finite list of natural numbers (row $c$ lists the costs from
client $c$ to the locations), and natural numbers $K$, the bound on the number of locations, and
$B$, the radius. -/
abbrev KCenterInstance := List (List ℕ) × ℕ × ℕ

/-- **Well-formed k-center instances.** A k-center instance $(D, K, B)$ is well formed when all
rows of $D$ have the same length. -/
def WellFormed (i : KCenterInstance) : Prop :=
  ∀ row ∈ i.1, ∀ row' ∈ i.1, row.length = row'.length

/-- **Feasible k-center instances.** Let $(D, K, B)$ be a k-center instance with rows
$D_0, \dots, D_{m-1}$, and let $n$ be the length of $D_0$, with $n = 0$ if $m = 0$. For $c < m$
and a natural number $f$, write $D_c(f)$ for the entry of $D_c$ at position $f$, counting from
$0$, and set $D_c(f) = 0$ if $D_c$ has at most $f$ entries. The instance is feasible when there
is a set $S$ of at most $K$ locations $f < n$ such that every client $c < m$ has some $f \in S$
with $D_c(f) \le B$. -/
def KCenterFeasible
    (i : KCenterInstance) : Prop :=
  ∃ facilities : List ℕ, facilities.Nodup ∧ facilities.length ≤ i.2.1 ∧
    (∀ f ∈ facilities, f < (i.1.getD 0 []).length) ∧
    ∃ assign : List ℕ, assign.length = i.1.length ∧
      ∀ c < i.1.length, assign.getD c 0 ∈ facilities ∧
        (i.1.getD c []).getD (assign.getD c 0) 0 ≤ i.2.2

open Classical in
/-- **Generalized nonmetric k-center as a decision problem.** This decision problem accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a k-center
instance that is well formed and feasible; bitstrings that do not decode to an instance are
rejected. -/
noncomputable def kCenterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KCenterInstance) x with
  | some i => decide (WellFormed i ∧ KCenterFeasible i)
  | none => false

/-- **k-CENTER (GENERALIZED, NONMETRIC) is NP-complete.** The decision problem of generalized
nonmetric k-center on bitstrings is NP-complete: it belongs to NP, and every decision problem in
NP has a polynomial-time many-one reduction to it.

Source: O. Kariv and S. L. Hakimi,
"An algorithmic approach to network location problems. I: The p-centers", SIAM Journal on
Applied Mathematics 37 (1979), 513-538. -/
public theorem_wanted kCenter_npComplete :
    kCenterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kCenterDec

end MetaMathlibExt.Complexity.NPComplete.KCenter

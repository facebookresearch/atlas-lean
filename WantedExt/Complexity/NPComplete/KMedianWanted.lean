/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-MEDIAN (GENERALIZED, NONMETRIC) is NP-complete

Source:
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. II: The
p-medians", SIAM Journal on Applied Mathematics 37 (1979), 539-560.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KMedian

/-!
# k-MEDIAN (GENERALIZED, NONMETRIC) is NP-complete

Generalized, nonmetric k-median: client-to-location costs (an arbitrary rectangular matrix of
natural numbers, one row per client, no metric assumed, clients and facilities distinct sets),
a bound `K` on the number of open locations, and a budget `B`. The question is whether at most
`K` locations can be opened so that the sum of each client's cost to its assigned open location
is at most `B`, witnessed by an assignment of each client to an open location. The metric
p-median problem of Kariv-Hakimi is the special case of a metric cost matrix; hardness follows
from that subclass (e.g. the dominating-set reduction with costs 1 on edges, 2 on nonedges, 0
on the diagonal).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **k-median instances.** A k-median instance is a triple $(d, K, B)$ of a cost matrix $d$, given
as a list of rows of natural numbers (one row per client, one entry per location; the rows need
not have equal length), a natural number $K$ bounding the number of open locations, and a
natural-number budget $B$. -/
abbrev KMedianInstance := List (List ℕ) × ℕ × ℕ

/-- **Well-formed k-median instances.** A k-median instance $(d, K, B)$ is well formed when all
rows of its cost matrix $d$ have the same length. -/
def WellFormed (i : KMedianInstance) : Prop :=
  ∀ row ∈ i.1, ∀ row' ∈ i.1, row.length = row'.length

/-- **Feasible k-median instances.** Let $(d, K, B)$ be a k-median instance whose cost matrix $d$
has rows $d_0, \dots, d_{n-1}$, one per client, and let $m$ be the length of $d_0$, or $m = 0$
when $n = 0$. The instance is feasible when there are a set $S \subseteq \{0, \dots, m-1\}$ of at
most $K$ locations and a choice of $a(c) \in S$ for each client $c < n$ such that
$\sum_{c < n} d_c(a(c)) \le B$, where $d_c(j)$ is the entry of $d_c$ at index $j$ (counting from
$0$), read as $0$ when $d_c$ has fewer than $j + 1$ entries. -/
def KMedianFeasible
    (i : KMedianInstance) : Prop :=
  ∃ facilities : List ℕ, facilities.Nodup ∧ facilities.length ≤ i.2.1 ∧
    (∀ f ∈ facilities, f < (i.1.getD 0 []).length) ∧
    ∃ assign : List ℕ, assign.length = i.1.length ∧
      (∀ c < i.1.length, assign.getD c 0 ∈ facilities) ∧
      (Finset.range i.1.length).sum
        (fun c => (i.1.getD c []).getD (assign.getD c 0) 0) ≤ i.2.2

open Classical in
/-- **The k-MEDIAN decision problem.** k-MEDIAN (generalized, nonmetric) is the decision problem
that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to
a k-median instance $(d, K, B)$ that is well formed and feasible. That is, $d$ has rows
$d_0, \dots, d_{n-1}$ (the clients) of a common length $m$ (the locations), and there are a set
$S \subseteq \{0, \dots, m-1\}$ of at most $K$ locations and a choice of $a(c) \in S$ for each
client $c < n$ with $\sum_{c < n} d_{c, a(c)} \le B$. Bitstrings that do not decode are
rejected. -/
noncomputable def kMedianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KMedianInstance) x with
  | some i => decide (WellFormed i ∧ KMedianFeasible i)
  | none => false

/-- **k-MEDIAN (GENERALIZED, NONMETRIC) is NP-complete.** The k-MEDIAN decision problem is in NP,
and every decision problem in NP has a polynomial-time many-one reduction to it.

Source: O. Kariv and S. L. Hakimi,
"An algorithmic approach to network location problems. II: The p-medians", SIAM Journal on
Applied Mathematics 37 (1979), 539-560. -/
public theorem_wanted kMedian_npComplete :
    kMedianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kMedianDec

end MetaMathlibExt.Complexity.NPComplete.KMedian

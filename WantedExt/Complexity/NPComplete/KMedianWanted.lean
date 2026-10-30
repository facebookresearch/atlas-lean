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

/-- A k-median instance: distance matrix, number of locations K, budget. -/
abbrev KMedianInstance := List (List ℕ) × ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : KMedianInstance) : Prop :=
  ∀ row ∈ i.1, ∀ row' ∈ i.1, row.length = row'.length

/-- At most `K` locations with total distance at most `B`. -/
def KMedianFeasible
    (i : KMedianInstance) : Prop :=
  ∃ facilities : List ℕ, facilities.Nodup ∧ facilities.length ≤ i.2.1 ∧
    (∀ f ∈ facilities, f < (i.1.getD 0 []).length) ∧
    ∃ assign : List ℕ, assign.length = i.1.length ∧
      (∀ c < i.1.length, assign.getD c 0 ∈ facilities) ∧
      (Finset.range i.1.length).sum
        (fun c => (i.1.getD c []).getD (assign.getD c 0) 0) ≤ i.2.2

open Classical in
/-- k-MEDIAN (GENERALIZED, NONMETRIC) as a decision problem over bitstrings. -/
noncomputable def kMedianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KMedianInstance) x with
  | some i => decide (WellFormed i ∧ KMedianFeasible i)
  | none => false

/-- **k-MEDIAN (GENERALIZED, NONMETRIC) is NP-complete.** Source: O. Kariv and S. L. Hakimi,
"An algorithmic approach to network location problems. II: The p-medians", SIAM Journal on
Applied Mathematics 37 (1979), 539-560. -/
public theorem_wanted kMedian_npComplete :
    kMedianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kMedianDec

end MetaMathlibExt.Complexity.NPComplete.KMedian

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONROE MULTIWINNER (approval misrepresentation) is NP-complete

Source:
A. D. Procaccia, J. S. Rosenschein and A. Zohar, "On the complexity of achieving proportional
representation", Social Choice and Welfare 30 (2008), 353-362, doi:10.1007/s00355-007-0235-2;
N. Betzler, A. Slinko and J. Uhlmann, "On the computation of fully proportional
representation", Journal of Artificial Intelligence Research 47 (2013), 475-519,
doi:10.1613/jair.3896, Section 1.1 (problem M-Multiwinner) and Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonroeApproval

/-!
# MONROE MULTIWINNER (approval misrepresentation) is NP-complete

Winner determination for Monroe's proportional representation scheme. INSTANCE: a set `C` of
candidates, a multiset `V` of `n` voters, the approval misrepresentation function `r`, a
misrepresentation bound `R`, and a positive integer `k`. QUESTION: is there a subset `C' ⊆ C` of
size `k` and an assignment `w : V → C` of voters to representatives that respects the Monroe
criterion, with `w(V) = C'` and `∑_{v ∈ V} r(v, w(v)) ≤ R`? The assignment respects the Monroe
criterion if `|w(V)| = k` and `w` assigns at least `⌊n/k⌋` and at most `⌈n/k⌉` voters to every
candidate of `w(V)`. Under the approval misrepresentation function a voter's misrepresentation
is `0` when represented by a candidate it approves and `1` otherwise, so the total
misrepresentation is the number of voters whose representative they do not approve.

The candidates are `0, …, m - 1`, and each voter is given by its approval vector, a list of `m`
Booleans (entry `c` is `true` when the voter approves candidate `c`); `V` is a list, so equal
votes may repeat. The total misrepresentation is an integer, so the bound `R` (a non-negative
rational in the source) is given as a natural number. `⌈n/k⌉` is `(n + k - 1) / k` for `k > 0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of candidates, the voters' approval vectors, the committee size
`k`, and the misrepresentation bound `R`. -/
abbrev MonroeApprovalInstance := ℕ × List (List Bool) × ℕ × ℕ

/-- Well-formedness of an instance: every approval vector has one entry per candidate, and `k` is
positive. -/
def WellFormed (i : MonroeApprovalInstance) : Prop :=
  (∀ v ∈ i.2.1, v.length = i.1) ∧ 0 < i.2.2.1

/-- The voters assigned to candidate `c` by `w`. -/
def assigned (i : MonroeApprovalInstance) (w : Fin i.2.1.length → Fin i.1) (c : Fin i.1) :
    Finset (Fin i.2.1.length) :=
  Finset.univ.filter fun v => w v = c

/-- The total approval misrepresentation of `w`: the number of voters who do not approve the
candidate representing them. -/
def misrepresentation (i : MonroeApprovalInstance) (w : Fin i.2.1.length → Fin i.1) : ℕ :=
  (Finset.univ.filter fun v => (i.2.1.get v).getD (w v) false = false).card

/-- Some committee `C'` of `k` candidates and some assignment `w` of the voters onto `C'`
respecting the Monroe criterion have total misrepresentation at most `R`. -/
def MonroeApprovalFeasible (i : MonroeApprovalInstance) : Prop :=
  ∃ C' : Finset (Fin i.1), C'.card = i.2.2.1 ∧
    ∃ w : Fin i.2.1.length → Fin i.1, (∀ v, w v ∈ C') ∧ (∀ c ∈ C', ∃ v, w v = c) ∧
      (∀ c ∈ C', i.2.1.length / i.2.2.1 ≤ (assigned i w c).card ∧
        (assigned i w c).card ≤ (i.2.1.length + i.2.2.1 - 1) / i.2.2.1) ∧
      misrepresentation i w ≤ i.2.2.2

open Classical in
/-- MONROE MULTIWINNER (approval misrepresentation) as a decision problem over bitstrings. -/
noncomputable def monroeApprovalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MonroeApprovalInstance) x with
  | some i => decide (WellFormed i ∧ MonroeApprovalFeasible i)
  | none => false

/-- **MONROE MULTIWINNER (approval misrepresentation) is NP-complete.** Source: Procaccia,
Rosenschein and Zohar (2008); Betzler, Slinko and Uhlmann (2013), Theorem 1. -/
public theorem_wanted monroeApproval_npComplete :
    monroeApprovalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L monroeApprovalDec

end MetaMathlibExt.Complexity.NPComplete.MonroeApproval

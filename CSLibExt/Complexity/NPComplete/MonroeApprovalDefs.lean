/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONROE MULTIWINNER (approval misrepresentation): definitions

Source:
A. D. Procaccia, J. S. Rosenschein and A. Zohar, "On the complexity of achieving proportional
representation", Social Choice and Welfare 30 (2008), 353-362, doi:10.1007/s00355-007-0235-2;
N. Betzler, A. Slinko and J. Uhlmann, "On the computation of fully proportional
representation", Journal of Artificial Intelligence Research 47 (2013), 475-519,
doi:10.1613/jair.3896, Section 1.1 (problem M-Multiwinner) and Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonroeApproval

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

end MetaMathlibExt.Complexity.NPComplete.MonroeApproval

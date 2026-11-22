/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED ASSIGNMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GENERALIZED ASSIGNMENT
PROBLEM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedAssignment

/-!
# GENERALIZED ASSIGNMENT is NP-complete

Jobs with per-machine resource consumptions and assignment costs, per-machine capacities, and a
cost bound `K`. The question is whether every job can be assigned to one machine so that no
machine's capacity is exceeded and the total assignment cost is at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A generalized-assignment instance: resource matrix (job by machine), cost matrix, machine
capacities, cost bound. -/
abbrev GeneralizedAssignmentInstance := List (List ℕ) × List (List ℕ) × List ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : GeneralizedAssignmentInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.2.2.1.length) ∧
    (∀ row ∈ i.2.1, row.length = i.2.2.1.length) ∧ i.1.length = i.2.1.length

/-- An assignment within capacities of total cost at most `K`. -/
def GeneralizedAssignmentFeasible
    (i : GeneralizedAssignmentInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1.length ∧
    (∀ j < i.1.length, assign.getD j 0 < i.2.2.1.length) ∧
    (∀ m < i.2.2.1.length,
      (Finset.range i.1.length).sum (fun j =>
        if assign.getD j 0 = m then (i.1.getD j []).getD m 0 else 0) ≤
        i.2.2.1.getD m 0) ∧
    (Finset.range i.1.length).sum
      (fun j => (i.2.1.getD j []).getD (assign.getD j 0) 0) ≤ i.2.2.2

open Classical in
/-- GENERALIZED ASSIGNMENT as a decision problem over bitstrings. -/
noncomputable def generalizedAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralizedAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ GeneralizedAssignmentFeasible i)
  | none => false

/-- **GENERALIZED ASSIGNMENT is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), GENERALIZED ASSIGNMENT PROBLEM. -/
public theorem_wanted generalizedAssignment_npComplete :
    generalizedAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalizedAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.GeneralizedAssignment

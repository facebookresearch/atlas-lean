/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED ASSIGNMENT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GENERALIZED ASSIGNMENT
PROBLEM.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedAssignment

/-- **Generalized-assignment instances.** A generalized-assignment instance is a tuple
$(R, C, c, K)$ where $R$ and $C$ are finite lists of finite lists of natural numbers, read as
matrices indexed by job and machine ($R_{j,i}$ is the resource job $j$ consumes on machine $i$
and $C_{j,i}$ is the cost of assigning job $j$ to machine $i$), $c$ is a finite list of natural
numbers (the machine capacities $c_i$), and $K$ is a natural number (the cost bound). -/
abbrev GeneralizedAssignmentInstance := List (List ℕ) × List (List ℕ) × List ℕ × ℕ

/-- **Well-formed generalized-assignment instances.** A generalized-assignment instance
$(R, C, c, K)$ is well formed when $R$ and $C$ have the same number of rows and every row of $R$
and every row of $C$ has as many entries as $c$ (one per machine). -/
def WellFormed (i : GeneralizedAssignmentInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.2.2.1.length) ∧
    (∀ row ∈ i.2.1, row.length = i.2.2.1.length) ∧ i.1.length = i.2.1.length

/-- **Feasible generalized assignments.** Let $(R, C, c, K)$ be a generalized-assignment instance,
let $n$ be the number of rows of $R$ (the jobs) and $m$ the length of $c$ (the machines), and
read entries missing from $R$ or $C$ as $0$. The instance is feasible when there are machines
$a_1, \dots, a_n \in \{1, \dots, m\}$ such that for every machine $i$ the sum of $R_{j,i}$
over the jobs $j$ with $a_j = i$ is at most $c_i$, and $\sum_{j=1}^{n} C_{j,a_j} \le K$. -/
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
/-- **The generalized assignment decision problem.** The decision problem GENERALIZED
ASSIGNMENT accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding of generalized-assignment instances, to an instance that is well formed and feasible.
Bitstrings that do not decode to an instance are rejected. -/
noncomputable def generalizedAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralizedAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ GeneralizedAssignmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeneralizedAssignment

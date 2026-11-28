/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW-SHOP SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS15] FLOW-SHOP SCHEDULING;
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129, doi:10.1287/moor.1.2.117.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling

/-- An instance: the number of processors `m`, one list of task lengths
`(l(t_1[j]), …, l(t_m[j]))` per job `j`, and the deadline `D`. -/
abbrev FlowShopSchedulingInstance := ℕ × List (List ℕ) × ℕ

/-- The length `l(t_i[j])` of the task of job `j` on processor `i`. -/
def len (i : FlowShopSchedulingInstance) (p : Fin i.1) (j : Fin i.2.1.length) : ℕ :=
  (i.2.1.getD j []).getD p 0

/-- Well-formedness of an instance: `0 < m`, every job has `m` tasks, and `0 < D`. -/
def WellFormed (i : FlowShopSchedulingInstance) : Prop :=
  0 < i.1 ∧ (∀ job ∈ i.2.1, job.length = i.1) ∧ 0 < i.2.2

/-- Some schedule `σ p j` (start of job `j`'s task on processor `p`) ends every task by `D`,
runs one task at a time on each processor, and runs each job's tasks in processor order. -/
def FlowShopSchedulingFeasible (i : FlowShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ,
    (∀ p j, σ p j + len i p j ≤ i.2.2) ∧
    (∀ p j k, j ≠ k → σ p j + len i p j ≤ σ p k ∨ σ p k + len i p k ≤ σ p j) ∧
    ∀ (p : Fin i.1) (hp : p.1 + 1 < i.1) j, σ p j + len i p j ≤ σ ⟨p.1 + 1, hp⟩ j

open Classical in
/-- FLOW-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def flowShopSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FlowShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ FlowShopSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling

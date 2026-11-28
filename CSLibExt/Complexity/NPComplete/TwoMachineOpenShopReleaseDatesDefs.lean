/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O2|r_i|Cmax: definitions

Source:
E. L. Lawler, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Minimizing maximum lateness in a
two-machine open shop", Mathematics of Operations Research 6 (1981), 153-158,
doi:10.1287/moor.6.1.153; Erratum, Mathematics of Operations Research 7 (1982), 635,
doi:10.1287/moor.7.4.635;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Open-shop problems without preemption" (`O2|r_i|C_max`, minimal NP-hard in the strong
sense, credited to Lawler, Lenstra, and Rinnooy Kan 1981, 1982);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING (the
parent problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs
public import CSLibExt.Complexity.NPComplete.TwoMachineFlowShopReleaseDatesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopReleaseDates

open TwoMachineFlowShopReleaseDates (TwoMachineFlowShopReleaseDatesInstance WellFormed)

/-- Some open-shop schedule `σ p j` (start of job `j`'s task on processor `p`) ends every task
by `K`, runs one task at a time on each processor, never runs the two tasks of a job at the same
time, and starts both tasks of every job `j` no earlier than its release date `rⱼ`. -/
def TwoMachineOpenShopReleaseDatesFeasible (i : TwoMachineFlowShopReleaseDatesInstance) :
    Prop :=
  ∃ σ : Fin i.1.1 → Fin i.1.2.1.length → ℕ,
    (∀ p j, σ p j + FlowShopScheduling.len i.1 p j ≤ i.1.2.2) ∧
    (∀ p j k, j ≠ k → σ p j + FlowShopScheduling.len i.1 p j ≤ σ p k ∨
      σ p k + FlowShopScheduling.len i.1 p k ≤ σ p j) ∧
    (∀ j p q, p ≠ q → σ p j + FlowShopScheduling.len i.1 p j ≤ σ q j ∨
      σ q j + FlowShopScheduling.len i.1 q j ≤ σ p j) ∧
    ∀ (p : Fin i.1.1) (j : Fin i.1.2.1.length), i.2.getD j 0 ≤ σ p j

open Classical in
/-- OPEN SHOP O2|r_i|Cmax as a decision problem over bitstrings. -/
noncomputable def twoMachineOpenShopReleaseDatesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineFlowShopReleaseDatesInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineOpenShopReleaseDatesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopReleaseDates

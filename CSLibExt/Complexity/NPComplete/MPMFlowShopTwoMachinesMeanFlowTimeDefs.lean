/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-PURPOSE MACHINE FLOW SHOP WITH TWO MACHINES TO MINIMIZE TOTAL COMPLETION TIME: definitions
# (`FMPM2||∑ Cᵢ`) is NP-complete

Source:
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129, doi:10.1287/moor.1.2.117 (the
two-machine flow shop `F2||∑ Cᵢ`, of which this problem is a generalization);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM flow shop
model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `FMPM2||∑ Cᵢ`, minimal NP-hard in the strong sense, Garey et al. (1976)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs
public import CSLibExt.Complexity.NPComplete.MPMFlowShopThreeMachinesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMFlowShopTwoMachinesMeanFlowTime

open MPMFlowShopThreeMachines (MPMFlowShopInstance MPMWellFormed IsMPMFlowShopSchedule)

/-- Well-formedness of an instance: a well-formed MPM flow shop instance with `m = 2` machines
(`0 < r`, every job has `r` operations, `0 < K`, one nonempty machine set per stage using
machines `0, 1`, pairwise different machine sets). -/
def WellFormed (i : MPMFlowShopInstance) : Prop :=
  MPMWellFormed 2 i

/-- Some MPM flow shop schedule in which operations on the same machine start at different
times has total completion time at most `K`: the sum over all jobs of the completion time
`σ p j + pⱼ` of the job's operation at the last stage `p` (`p + 1 = r`). -/
def MPMFlowShopTwoMachinesMeanFlowTimeFeasible (i : MPMFlowShopInstance) : Prop :=
  ∃ σ a : Fin i.1.1 → Fin i.1.2.1.length → ℕ, IsMPMFlowShopSchedule i σ a ∧
    (∀ p j q k, (p, j) ≠ (q, k) → a p j = a q k → σ p j ≠ σ q k) ∧
    ∀ p : Fin i.1.1, p.1 + 1 = i.1.1 →
      ∑ j, (σ p j + FlowShopScheduling.len i.1 p j) ≤ i.1.2.2

open Classical in
/-- MULTI-PURPOSE MACHINE FLOW SHOP WITH TWO MACHINES TO MINIMIZE TOTAL COMPLETION TIME as a
decision problem over bitstrings. -/
noncomputable def mpmFlowShopTwoMachinesMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMFlowShopInstance) x with
  | some i => decide (WellFormed i ∧ MPMFlowShopTwoMachinesMeanFlowTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPMFlowShopTwoMachinesMeanFlowTime

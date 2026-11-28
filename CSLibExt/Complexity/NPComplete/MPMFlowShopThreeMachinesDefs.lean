/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-PURPOSE MACHINE FLOW SHOP WITH THREE MACHINES (`FMPM3||C_max`): definitions

Source:
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129, doi:10.1287/moor.1.2.117 (the
three-machine flow shop `F3||C_max`, of which this problem is a generalization);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM flow shop
model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `FMPM3||C_max`, minimal NP-hard in the strong sense, Garey et al. (1976)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Dedup
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMFlowShopThreeMachines

/-- An MPM flow shop instance: a FLOW-SHOP SCHEDULING instance `(r, jobs, K)` (the number `r` of
stages, one list of the `r` operation processing times per job, and the bound `K`) and the
machine sets `μ₁, …, μᵣ` of the stages, as lists of machine indices. -/
abbrev MPMFlowShopInstance := FlowShopScheduling.FlowShopSchedulingInstance × List (List ℕ)

/-- The machine set `μ_p` of stage `p`. -/
def machineSet (i : MPMFlowShopInstance) (p : Fin i.1.1) : List ℕ :=
  i.2.getD p []

/-- Well-formedness of an MPM flow shop instance with `m` machines: the FLOW-SHOP SCHEDULING
instance is well-formed (`0 < r`, every job has `r` operations, `0 < K`), there is one machine
set per stage, every machine set is nonempty and contains only machines `0, …, m - 1`, and the
machine sets are pairwise different (as sets). -/
def MPMWellFormed (m : ℕ) (i : MPMFlowShopInstance) : Prop :=
  FlowShopScheduling.WellFormed i.1 ∧ i.2.length = i.1.1 ∧
    (∀ μ ∈ i.2, μ ≠ [] ∧ ∀ M ∈ μ, M < m) ∧ (i.2.map List.toFinset).Nodup

/-- `σ` and `a` form an MPM flow shop schedule: the operation of job `j` at stage `p` starts at
`σ p j` on machine `a p j ∈ μ_p`; two different operations on the same machine do not overlap;
and each job's operations run in stage order. -/
def IsMPMFlowShopSchedule (i : MPMFlowShopInstance)
    (σ a : Fin i.1.1 → Fin i.1.2.1.length → ℕ) : Prop :=
  (∀ p j, a p j ∈ machineSet i p) ∧
    (∀ p j q k, (p, j) ≠ (q, k) → a p j = a q k →
      σ p j + FlowShopScheduling.len i.1 p j ≤ σ q k ∨
        σ q k + FlowShopScheduling.len i.1 q k ≤ σ p j) ∧
    ∀ (p : Fin i.1.1) (hp : p.1 + 1 < i.1.1) j,
      σ p j + FlowShopScheduling.len i.1 p j ≤ σ ⟨p.1 + 1, hp⟩ j

/-- Well-formedness of an instance: a well-formed MPM flow shop instance with `m = 3`
machines. -/
def WellFormed (i : MPMFlowShopInstance) : Prop :=
  MPMWellFormed 3 i

/-- Some MPM flow shop schedule completes every operation by `K`. -/
def MPMFlowShopThreeMachinesFeasible (i : MPMFlowShopInstance) : Prop :=
  ∃ σ a : Fin i.1.1 → Fin i.1.2.1.length → ℕ, IsMPMFlowShopSchedule i σ a ∧
    ∀ p j, σ p j + FlowShopScheduling.len i.1 p j ≤ i.1.2.2

open Classical in
/-- MULTI-PURPOSE MACHINE FLOW SHOP WITH THREE MACHINES as a decision problem over
bitstrings. -/
noncomputable def mpmFlowShopThreeMachinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMFlowShopInstance) x with
  | some i => decide (WellFormed i ∧ MPMFlowShopThreeMachinesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPMFlowShopThreeMachines

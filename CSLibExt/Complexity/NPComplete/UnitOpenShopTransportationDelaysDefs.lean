/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP WITH TRANSPORTATION DELAYS O2|p_ij=1;t_i|Cmax: definitions

Source:
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996), Section 3.8, Theorem 2;
W. Yu, H. Hoogeveen and J. K. Lenstra, "Minimizing makespan in a two-machine flow shop with
delays and unit-time operations is NP-hard", Journal of Scheduling 7 (2004), 333-348,
doi:10.1023/B:JOSH.0000036858.59787.c2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopTransportationDelays

open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)
open UnitFlowShopTransportationDelays
  (UnitFlowShopTransportationDelaysInstance Job delay WellFormed)

/-- A schedule of a two-machine open shop with unit-time operations and delays `t`: `σ m j` is
the start time of job `j`'s operation on machine `M_{m+1}`; `σ` is a unit-time open-shop
schedule (`IsUnitOpenShopSchedule` with no precedence arcs: each machine, and each job, starts
its operations at different times), and the two operations of job `j`, in either order, are
separated by at least `t j`: the later one starts at least `t j` time units after the earlier
one completes. -/
def IsUnitOpenShopScheduleWithDelays {n : ℕ} (t : Fin n → ℕ) (σ : Fin 2 → Fin n → ℕ) : Prop :=
  IsUnitOpenShopSchedule 2 n [] σ ∧
    ∀ j, σ 0 j + 1 + t j ≤ σ 1 j ∨ σ 1 j + 1 + t j ≤ σ 0 j

/-- Some open-shop schedule with the job delays completes every operation by `K`. -/
def UnitOpenShopTransportationDelaysFeasible
    (i : UnitFlowShopTransportationDelaysInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitOpenShopScheduleWithDelays (delay i) σ ∧
    ∀ m j, σ m j + 1 ≤ i.2

open Classical in
/-- OPEN SHOP WITH TRANSPORTATION DELAYS `O2|p_ij=1;t_i|C_max` as a decision problem over
bitstrings. -/
noncomputable def unitOpenShopTransportationDelaysDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopTransportationDelaysInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopTransportationDelaysFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopTransportationDelays

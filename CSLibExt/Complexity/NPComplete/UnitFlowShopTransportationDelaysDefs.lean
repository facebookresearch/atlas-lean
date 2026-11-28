/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP WITH TRANSPORTATION DELAYS F2|p_ij=1;t_i|Cmax: definitions

Source:
W. Yu, H. Hoogeveen and J. K. Lenstra, "Minimizing makespan in a two-machine flow shop with
delays and unit-time operations is NP-hard", Journal of Scheduling 7 (2004), 333-348,
doi:10.1023/B:JOSH.0000036858.59787.c2;
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopTransportationDelays

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- A schedule of a two-machine flow shop with unit-time operations and delays `t`: `σ m j` is
the start time of job `j`'s operation on machine `M_{m+1}`; each machine runs a one-processor
schedule of its unit-time operations, and job `j`'s second operation starts at least `t j` time
units after its first operation completes. With `t = 0` this is an ordinary schedule of the
unit-time two-machine flow shop. -/
def IsUnitFlowShopSchedule {n : ℕ} (t : Fin n → ℕ) (σ : Fin 2 → Fin n → ℕ) : Prop :=
  (∀ m, IsOneProcessorSchedule (fun _ => 1) (σ m)) ∧ ∀ j, σ 0 j + 1 + t j ≤ σ 1 j

/-- An instance: the delays `t_j`, one per job, and the bound `K`. -/
abbrev UnitFlowShopTransportationDelaysInstance := List ℕ × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed delays. -/
abbrev Job (i : UnitFlowShopTransportationDelaysInstance) : Type := Fin i.1.length

/-- The delay `t_j` of job `j`. -/
def delay (i : UnitFlowShopTransportationDelaysInstance) (j : Job i) : ℕ :=
  i.1.get j

/-- Well-formedness of an instance: every list of delays with a bound is an instance (delays
are non-negative integers, and the bound needs no condition). -/
def WellFormed (_i : UnitFlowShopTransportationDelaysInstance) : Prop :=
  True

/-- Some schedule completes every operation by `K`: every second operation, which completes
after the first operation of its job, ends by time `K`. -/
def UnitFlowShopTransportationDelaysFeasible
    (i : UnitFlowShopTransportationDelaysInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitFlowShopSchedule (delay i) σ ∧ ∀ j, σ 1 j + 1 ≤ i.2

open Classical in
/-- FLOW SHOP WITH TRANSPORTATION DELAYS `F2|p_ij=1;t_i|C_max` as a decision problem over
bitstrings. -/
noncomputable def unitFlowShopTransportationDelaysDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopTransportationDelaysInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopTransportationDelaysFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopTransportationDelays

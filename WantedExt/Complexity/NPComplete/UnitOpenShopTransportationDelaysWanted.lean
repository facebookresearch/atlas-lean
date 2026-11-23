/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP WITH TRANSPORTATION DELAYS O2|p_ij=1;t_i|Cmax is NP-complete

Source:
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996), Section 3.8, Theorem 2;
W. Yu, H. Hoogeveen and J. K. Lenstra, "Minimizing makespan in a two-machine flow shop with
delays and unit-time operations is NP-hard", Journal of Scheduling 7 (2004), 333-348,
doi:10.1023/B:JOSH.0000036858.59787.c2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysWanted
public import WantedExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopTransportationDelays

open UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)
open UnitFlowShopTransportationDelays
  (UnitFlowShopTransportationDelaysInstance Job delay WellFormed)

/-!
# OPEN SHOP WITH TRANSPORTATION DELAYS O2|p_ij=1;t_i|Cmax is NP-complete

INSTANCE: `n` jobs, each consisting of two unit-time operations, one on machine `M₁` and one on
machine `M₂`, which may be processed in either order but not at the same time; for each job `j`
a delay `t_j ∈ ℤ₀⁺`; a bound `K`. Each machine processes at most one operation at a time, and
the operation of job `j` processed second cannot start until `t_j` time units after the
completion of the operation processed first (the delay uses no machine, and any number of jobs
can be in transit at once). QUESTION: is there a schedule whose makespan, the largest completion
time of an operation, is at most `K`?

This is the decision version of `O2|p_ij=1, l_j|C_max` in Yu (1996), Section 3.8, whose delays
`l_j` are minimum time lags between the completion of the operation processed first and the
start of the operation processed second; Yu proves it strongly NP-hard (Theorem 2 of Section
3.8) by a reduction from 3-PARTITION that builds on the flow-shop result `F2|p_ij=1, l_j|C_max`,
published in Yu, Hoogeveen and Lenstra (2004). Brucker and Knust's scheduling classification
writes the problem `O2|p_ij=1; t_i|C_max` (transportation delays) and cites both.

The instance, the jobs, the delays and the well-formedness (every list of delays with a bound
is an instance) are those of the flow shop `F2|p_ij=1; t_i|C_max`
(`UnitFlowShopTransportationDelaysWanted`); only the schedule differs, since in an open shop
each job chooses the order of its two operations. Start times are natural numbers: with integer
delays and unit operations, fixing the order of the operations on each machine and within each
job, and starting every operation as early as these orders and the delays allow, gives an
integral schedule whose completion times are no later, so this does not change the answer.
The schedule is the unit-time open-shop schedule `IsUnitOpenShopSchedule` of
`UnitOpenShopOutTreeMaxLatenessWanted` on two machines with no precedence arcs (the operations
on one machine, and the two operations of one job, start at different times), plus the delay
condition, which for a job with delay `t_j` asks that the operation processed second start at
least `t_j` after the operation processed first completes. Binary encoding of all numbers (the
problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **OPEN SHOP WITH TRANSPORTATION DELAYS `O2|p_ij=1;t_i|C_max` is NP-complete.** Source:
Yu (1996), Section 3.8, Theorem 2; Yu, Hoogeveen and Lenstra (2004). -/
public theorem_wanted unitOpenShopTransportationDelays_npComplete :
    unitOpenShopTransportationDelaysDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopTransportationDelaysDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopTransportationDelays

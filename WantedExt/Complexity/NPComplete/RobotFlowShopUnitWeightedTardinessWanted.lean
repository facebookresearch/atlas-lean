/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=1;t_i|Σw_iT_i (two-machine unit flow shop, single transport robot, total weighted
tardiness) is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_1ro` (flow-shop problems with transportation times and a single robot), Universität
Osnabrück (last update 2004), entry `F2;R1|p_ij=1;t_i|Σw_iT_i` (minimal NP-hard, strongly),
citing S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität
Osnabrück, Fachbereich Mathematik/Informatik (1999) (the thesis text was not available);
robot model: J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with
transportation times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitWeightedTardiness

open UnitFlowShopTransportationDelays (IsUnitFlowShopSchedule)

/-!
# F2;R1|p_ij=1;t_i|Σw_iT_i is NP-complete

INSTANCE: two machines `M₁, M₂` in a flow shop and `n` jobs, each job `j` consisting of an
operation of unit length on `M₁` (`p₁ⱼ = 1`) followed by an operation of unit length on `M₂`
(`p₂ⱼ = 1`), each machine processing at most one operation at a time; between its two
operations job `j` is transported from `M₁` to `M₂` by a single robot, the transport taking
`tⱼ ∈ ℤ₀⁺`; each job `j` has a due date `dⱼ ∈ ℤ₀⁺` and a weight `wⱼ ∈ ℤ₀⁺`; and a bound `K`.
QUESTION: is there a feasible schedule whose total weighted tardiness
`Σⱼ wⱼ · max(0, Cⱼ - dⱼ)` is at most `K`, where `Cⱼ` is the completion time of job `j` on `M₂`?

The robot model is that of Hurink and Knust (2001), Section 1: one robot carries every job from
`M₁` to `M₂`, at most one job at a time, the transport of job `j` taking `tⱼ` time units; empty
moves of the robot take no time; buffers before and after the machines are unlimited, so a job
may wait for the robot and for `M₂`. A schedule gives the start times `σ 0 j`, `σ 1 j` of job
`j`'s operations on `M₁`, `M₂` and the start time `ρ j` of its transport
(`IsUnitRobotFlowShopSchedule`). The machines then run a schedule of the unit-time flow shop
with transportation delays `t` (`IsUnitFlowShopSchedule` of `UnitFlowShopTransportationDelays`,
where any number of jobs may be in transit at once); the single robot adds that each transport
starts after the job's operation on `M₁` and ends by the start of its operation on `M₂`, and that
the transports of distinct jobs do not overlap (in the pairwise form of FLOW-SHOP SCHEDULING,
which the robot instances `RobotFlowShopConstantTransport` and `RobotFlowShopEqualProcessing`
use through their three-machine view). `Cⱼ = σ 1 j + 1`, and `Cⱼ - dⱼ` in `ℕ` is
`max(0, Cⱼ - dⱼ)`. Start times are natural numbers: with integer data, starting every operation
as early as the order of the operations on `M₁`, on the robot and on `M₂` allows gives an
integral schedule whose completion times are no later, so this does not change the answer.
Every decoded instance is well formed (all data, `K` included, are non-negative integers).
The jobs are `Fin n`, one per listed triple. Binary encoding of all numbers.

Membership in NP: some optimal schedule starts every operation by
`Σⱼ (tⱼ + 2)`, so start times form a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A schedule of the two-machine flow shop with unit-time operations and a single transport
robot: `σ 0 j` and `σ 1 j` are the start times of job `j`'s operations on `M₁` and `M₂`, and
`ρ j` is the start time of its transport, which takes `t j`. The machines run a schedule of the
unit-time flow shop with delays `t`; each transport starts once the job's operation on `M₁`
completes and ends by the start of its operation on `M₂`; and the robot carries one job at a
time: the transports of distinct jobs do not overlap. -/
def IsUnitRobotFlowShopSchedule {n : ℕ} (t : Fin n → ℕ) (σ : Fin 2 → Fin n → ℕ)
    (ρ : Fin n → ℕ) : Prop :=
  IsUnitFlowShopSchedule t σ ∧
    (∀ j, σ 0 j + 1 ≤ ρ j ∧ ρ j + t j ≤ σ 1 j) ∧
    ∀ j k, j ≠ k → ρ j + t j ≤ ρ k ∨ ρ k + t k ≤ ρ j

/-- An instance: the jobs, job `j` being the `j`-th triple `(tⱼ, dⱼ, wⱼ)` of its transport
time, due date and weight, and the bound `K`. -/
abbrev RobotFlowShopUnitWeightedTardinessInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed triples. -/
abbrev Job (i : RobotFlowShopUnitWeightedTardinessInstance) : Type := Fin i.1.length

/-- The transport time `tⱼ` of job `j`. -/
def transportTime (i : RobotFlowShopUnitWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The due date `dⱼ` of job `j`. -/
def dueDate (i : RobotFlowShopUnitWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The weight `wⱼ` of job `j`. -/
def weight (i : RobotFlowShopUnitWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Well-formedness: every instance (all data are non-negative integers). -/
def WellFormed (_ : RobotFlowShopUnitWeightedTardinessInstance) : Prop := True

/-- Some single-robot schedule has total weighted tardiness `Σⱼ wⱼ · max(0, Cⱼ - dⱼ)` at most
`K`, where `Cⱼ = σ 1 j + 1`. -/
def RobotFlowShopUnitWeightedTardinessFeasible
    (i : RobotFlowShopUnitWeightedTardinessInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, ∃ ρ : Job i → ℕ,
    IsUnitRobotFlowShopSchedule (transportTime i) σ ρ ∧
      ∑ j, weight i j * (σ 1 j + 1 - dueDate i j) ≤ i.2

open Classical in
/-- F2;R1|p_ij=1;t_i|Σw_iT_i as a decision problem over bitstrings. -/
noncomputable def robotFlowShopUnitWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopUnitWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopUnitWeightedTardinessFeasible i)
  | none => false

/-- **F2;R1|p_ij=1;t_i|Σw_iT_i is NP-complete.**
Source: Brucker and Knust's classification, class `f_1ro`, citing Knust (1999); robot model of
Hurink and Knust (2001). -/
public theorem_wanted robotFlowShopUnitWeightedTardiness_npComplete :
    robotFlowShopUnitWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopUnitWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitWeightedTardiness

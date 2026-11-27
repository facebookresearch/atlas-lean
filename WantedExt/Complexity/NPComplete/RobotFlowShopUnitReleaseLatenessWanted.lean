/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=1;t_i;r_i|L_max (two-machine unit flow shop, single transport robot, release dates,
maximum lateness) is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_1ro` (flow-shop problems with transportation times and a single robot), Universität
Osnabrück (last update 2004), entry `F2;R1|p_ij=1;t_i;r_i|L_max` (minimal NP-hard,
strongly), citing S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität
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
public import WantedExt.Complexity.NPComplete.RobotFlowShopUnitWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitReleaseLateness

open RobotFlowShopUnitWeightedTardiness (IsUnitRobotFlowShopSchedule)

/-!
# F2;R1|p_ij=1;t_i;r_i|L_max is NP-complete

INSTANCE: two machines `M₁, M₂` in a flow shop and `n` jobs, each job `j` consisting of an
operation of unit length on `M₁` (`p₁ⱼ = 1`) followed by an operation of unit length on `M₂`
(`p₂ⱼ = 1`), each machine processing at most one operation at a time; between its two
operations job `j` is transported from `M₁` to `M₂` by a single robot, the transport taking
`tⱼ ∈ ℤ₀⁺`; each job `j` has a release date `rⱼ ∈ ℤ₀⁺`, before which it cannot start, and a due date
`dⱼ ∈ ℤ₀⁺`; and an integer `y`. QUESTION: is there a feasible schedule whose maximum lateness
`L_max = maxⱼ (Cⱼ - dⱼ)` is at most `y`, where `Cⱼ` is the completion time of job `j` on `M₂`?

The schedules are those of F2;R1|p_ij=1;t_i|Σw_iT_i (`IsUnitRobotFlowShopSchedule` of
`RobotFlowShopUnitWeightedTardiness`), with release dates added. The robot model is that of Hurink
and Knust (2001), Section 1: one robot carries every job from `M₁` to `M₂`, at most one job at a
time, the transport of job `j` taking `tⱼ` time units; empty moves of the robot take no time;
buffers before and after the machines are unlimited. A schedule gives the start times `σ 0 j`,
`σ 1 j` of job `j`'s operations on `M₁`, `M₂` and the start time `ρ j` of its transport: the
machines run a schedule of the unit-time flow shop with transportation delays `t`, each transport
starts after the job's operation on `M₁` and ends by the start of its operation on `M₂`, and the
transports of distinct jobs do not overlap. Job `j` starts on `M₁` no earlier than `rⱼ`.
`Cⱼ = σ 1 j + 1`. The bound `y` is an integer, encoded as a pair `(y⁺, y⁻)` of naturals representing
`y⁺ - y⁻`, as in `TwoProcessorFlowShopMaximumLatenessWanted`; `Cⱼ - dⱼ ≤ y⁺ - y⁻` is stated over `ℕ`
as `Cⱼ + y⁻ ≤ dⱼ + y⁺`. Start times are natural numbers: with integer data, starting every operation
as early as the release dates and the order of the operations on `M₁`, on the robot and on `M₂`
allow gives an integral schedule whose completion times are no later, so this does not change the
answer. An instance is well formed when it has at least one job, so that `L_max` is a maximum over a
nonempty set (release dates, transport times and due dates are non-negative integers, and `y` is any
integer). The jobs are `Fin n`, one per listed triple. Binary encoding of all numbers.

Membership in NP: some optimal schedule starts every operation by `maxⱼ rⱼ + Σⱼ (tⱼ + 2)`, so
start times form a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs, job `j` being the `j`-th triple `(rⱼ, tⱼ, dⱼ)` of its release date,
transport time and due date, and the bound `y` as a pair `(y⁺, y⁻)` with `y = y⁺ - y⁻`. -/
abbrev RobotFlowShopUnitReleaseLatenessInstance := List (ℕ × ℕ × ℕ) × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed triples. -/
abbrev Job (i : RobotFlowShopUnitReleaseLatenessInstance) : Type := Fin i.1.length

/-- The release date `rⱼ` of job `j`. -/
def releaseDate (i : RobotFlowShopUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The transport time `tⱼ` of job `j`. -/
def transportTime (i : RobotFlowShopUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The due date `dⱼ` of job `j`. -/
def dueDate (i : RobotFlowShopUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Well-formedness: there is at least one job, so that `L_max` is a maximum over a nonempty set
(release dates, transport times and due dates are non-negative integers, and the bound
`y⁺ - y⁻` is an arbitrary integer). -/
def WellFormed (i : RobotFlowShopUnitReleaseLatenessInstance) : Prop := i.1 ≠ []

/-- Some single-robot schedule starts every job on `M₁` no earlier than its release date and
completes every job `j` with lateness `Cⱼ - dⱼ ≤ y⁺ - y⁻`, where `Cⱼ = σ 1 j + 1`. -/
def RobotFlowShopUnitReleaseLatenessFeasible (i : RobotFlowShopUnitReleaseLatenessInstance) :
    Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, ∃ ρ : Job i → ℕ,
    IsUnitRobotFlowShopSchedule (transportTime i) σ ρ ∧
      (∀ j, releaseDate i j ≤ σ 0 j) ∧
      ∀ j, σ 1 j + 1 + i.2.2 ≤ dueDate i j + i.2.1

open Classical in
/-- F2;R1|p_ij=1;t_i;r_i|L_max as a decision problem over bitstrings. -/
noncomputable def robotFlowShopUnitReleaseLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopUnitReleaseLatenessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopUnitReleaseLatenessFeasible i)
  | none => false

/-- **F2;R1|p_ij=1;t_i;r_i|L_max is NP-complete.**
Source: Brucker and Knust's classification, class `f_1ro`, citing Knust (1999); robot model of
Hurink and Knust (2001). -/
public theorem_wanted robotFlowShopUnitReleaseLateness_npComplete :
    robotFlowShopUnitReleaseLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopUnitReleaseLatenessDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitReleaseLateness

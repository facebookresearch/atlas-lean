/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, MAXIMUM LATENESS WITH RELEASE DATES `F3;R1|p_ij=1;t_ik;r_i|L_max` is
# NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik;r_i|L_max` (minimal NP-hard
in the strong sense, citing Knust 1999);
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (the robot model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesUnitReleaseLateness

open RobotFlowShopThreeMachinesWeightedTardiness (IsRobotSchedule)

/-!
# ROBOT FLOW SHOP, MAXIMUM LATENESS WITH RELEASE DATES `F3;R1|p_ij=1;t_ik;r_i|L_max`

INSTANCE: machines `M_1, M_2, M_3` in a flow shop; jobs `1, …, n`, job `i` consisting of
operations `O_i1, O_i2, O_i3` of unit length (`p_ij = 1`), `O_ij` processed on `M_j`; each
machine processes at most one operation at a time; between `M_k` and `M_(k+1)` (`k = 1, 2`) job
`i` is carried by a single transport robot, the transport taking `t_ik ∈ ℤ₀⁺` time units; the
robot carries at most one job at a time; job `i` has a release date `r_i ∈ ℤ₀⁺`, before which
it cannot start, and a due date `d_i ∈ ℤ₀⁺`; and an integer `y`. QUESTION: is there a feasible
schedule whose maximum lateness `L_max = max_i (C_i - d_i)` is at most `y`, where `C_i` is the
completion time of `O_i3`?

The robot model is that of Hurink and Knust (Section 1): one robot transports every job between
consecutive machines, handles one job at a time, its empty moves take no time, and buffers are
unlimited. Brucker and Knust record `F3;R1|p_ij=1;t_ik;r_i|L_max` as minimal NP-hard in the
strong sense, credited to Knust's thesis (1999), which was not available.

Encoding. The schedules are those of `F3;R1|p_ij=1;t_ik|Σw_iT_i`
(`IsRobotSchedule` of `RobotFlowShopThreeMachinesWeightedTardinessWanted`), with release dates
added. Jobs are listed one per entry as `(t_i1, t_i2, r_i, d_i)`; jobs are `Fin n`.
`IsRobotSchedule` reads from its instance only the job list and the first two entries of each
job (the transport times), so it is applied to `(jobs, 0)`. A schedule gives job `i` start
times `a i`, `c i`, `f i` of its operations on `M_1`, `M_2`, `M_3` and start times `b i`, `e i`
of its two transports: a job's steps follow each other (`a i + 1 ≤ b i`, `b i + t_i1 ≤ c i`,
`c i + 1 ≤ e i`, `e i + t_i2 ≤ f i`), start times on each machine are pairwise different (unit
operations), and the `2n` transports occupy pairwise disjoint sets of time units. Job `i` starts
on `M_1` no earlier than `r_i`, and `C_i = f i + 1`. The bound `y` is an integer, encoded as a
pair `(y⁺, y⁻)` of naturals representing `y⁺ - y⁻`, as in `RobotFlowShopUnitReleaseLatenessWanted`
(`F2;R1|p_ij=1;t_i;r_i|L_max`); `C_i - d_i ≤ y⁺ - y⁻` is stated over `ℕ` as
`C_i + y⁻ ≤ d_i + y⁺`. An instance is well formed when it has at least one job, so that `L_max`
is a maximum over a nonempty set. With integer data, starting every step as early as the release
dates and the orders on the machines and on the robot allow gives an integral schedule with no
later completion times, so integer start times lose no generality. Membership in NP: some
optimal schedule starts every step by `max_i r_i + ∑_i (3 + t_i1 + t_i2)`, so start times form a
certificate of polynomial size. Binary encoding of all numbers (the problem is NP-hard in the
strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs `(t_i1, t_i2, r_i, d_i)` (transport times from `M_1` to `M_2` and from
`M_2` to `M_3`, release date, due date), one per entry, and the bound `y` as a pair `(y⁺, y⁻)`
with `y = y⁺ - y⁻`. -/
abbrev RobotFlowShopThreeMachinesUnitReleaseLatenessInstance :=
  List (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) : Type :=
  Fin i.1.length

/-- The release date `r_i` of job `i`. -/
def releaseDate (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2.1

/-- The due date `d_i` of job `i`. -/
def dueDate (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2.2

/-- Well-formedness: there is at least one job, so that `L_max` is a maximum over a nonempty set
(transport times, release dates and due dates are non-negative integers, and the bound
`y⁺ - y⁻` is an arbitrary integer). -/
def WellFormed (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) : Prop := i.1 ≠ []

/-- Some single-robot schedule starts every job on `M_1` no earlier than its release date and
completes every job `j` with lateness `C_j - d_j ≤ y⁺ - y⁻`, where `C_j = f j + 1`. -/
def RobotFlowShopThreeMachinesUnitReleaseLatenessFeasible
    (i : RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) : Prop :=
  ∃ a b c e f, IsRobotSchedule (i.1, 0) a b c e f ∧ (∀ j, releaseDate i j ≤ a j) ∧
    ∀ j, f j + 1 + i.2.2 ≤ dueDate i j + i.2.1

open Classical in
/-- `F3;R1|p_ij=1;t_ik;r_i|L_max` as a decision problem over bitstrings. -/
noncomputable def robotFlowShopThreeMachinesUnitReleaseLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesUnitReleaseLatenessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopThreeMachinesUnitReleaseLatenessFeasible i)
  | none => false

/-- **ROBOT FLOW SHOP, MAXIMUM LATENESS WITH RELEASE DATES `F3;R1|p_ij=1;t_ik;r_i|L_max` is
NP-complete.** Source: Knust (1999), as recorded by Brucker and Knust; Hurink and Knust (2001)
for the model. -/
public theorem_wanted robotFlowShopThreeMachinesUnitReleaseLateness_npComplete :
    robotFlowShopThreeMachinesUnitReleaseLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopThreeMachinesUnitReleaseLatenessDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesUnitReleaseLateness

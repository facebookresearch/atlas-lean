/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, TOTAL COMPLETION TIME WITH RELEASE DATES `F3;R1|p_ij=1;t_ik;r_i|ΣC_i` is
# NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik;r_i|ΣC_i` (minimal NP-hard
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

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesUnitReleaseCompletion

open RobotFlowShopThreeMachinesWeightedTardiness
  (RobotFlowShopThreeMachinesWeightedTardinessInstance Job IsRobotSchedule)

/-!
# ROBOT FLOW SHOP, TOTAL COMPLETION TIME WITH RELEASE DATES `F3;R1|p_ij=1;t_ik;r_i|ΣC_i`

INSTANCE: machines `M_1, M_2, M_3` in a flow shop; jobs `1, …, n`, job `i` consisting of
operations `O_i1, O_i2, O_i3` of unit length (`p_ij = 1`), `O_ij` processed on `M_j`; each
machine processes at most one operation at a time; between `M_k` and `M_(k+1)` (`k = 1, 2`) job
`i` is carried by a single transport robot, the transport taking `t_ik ∈ ℤ₀⁺` time units; the
robot carries at most one job at a time; job `i` has a release date `r_i ∈ ℤ₀⁺`, before which
it cannot start; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a feasible schedule with total
completion time `∑_i C_i ≤ K`, where `C_i` is the completion time of `O_i3`?

The robot model is that of Hurink and Knust (Section 1): one robot transports every job between
consecutive machines, handles one job at a time, its empty moves take no time, and buffers are
unlimited. Brucker and Knust record `F3;R1|p_ij=1;t_ik;r_i|ΣC_i` as minimal NP-hard in the
strong sense, credited to Knust's thesis (1999), which was not available.

Encoding. The schedules are those of `F3;R1|p_ij=1;t_ik|Σw_iT_i`
(`IsRobotSchedule` of `RobotFlowShopThreeMachinesWeightedTardinessWanted`), with release dates
added. An instance is an instance of that problem
(`RobotFlowShopThreeMachinesWeightedTardinessInstance`: jobs listed one per entry as four
numbers, and the bound `K`; its jobs `Job` are `Fin n`), whose
jobs are read here as `(t_i1, t_i2, r_i, w_i)`: transport times and weight as there, and the
third entry, there a due date, as the release date. `IsRobotSchedule` reads only the first two
entries of each job (the transport times). The question bounds `∑_i w_i C_i`, and
well-formedness asks for unit weights `w_i = 1`, so the objective is `∑_i C_i`. A schedule gives
job `i` start times `a i`, `c i`, `f i` of its operations on `M_1`, `M_2`, `M_3` and start times
`b i`, `e i` of its two transports: a job's steps follow each other (`a i + 1 ≤ b i`,
`b i + t_i1 ≤ c i`, `c i + 1 ≤ e i`, `e i + t_i2 ≤ f i`), start times on each machine are
pairwise different (unit operations), and the `2n` transports occupy pairwise disjoint sets of
time units. Job `i` starts on `M_1` no earlier than `r_i`, and `C_i = f i + 1`. With integer
data, starting every step as early as the release dates and the orders on the machines and on
the robot allow gives an integral schedule with no later completion times, so integer start
times lose no generality. Membership in NP: some optimal schedule starts every step by
`max_i r_i + ∑_i (3 + t_i1 + t_i2)`, so start times form a certificate of polynomial size.
Binary encoding of all numbers (the problem is NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The release date `r_i` of job `i`: the third entry of its tuple `(t_i1, t_i2, r_i, w_i)`. -/
def releaseDate (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2.1

/-- Well-formedness of an instance: every job has weight `1`. -/
def WellFormed (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∀ x ∈ i.1, x.2.2.2 = 1

/-- Some single-robot schedule starts every job on `M_1` no earlier than its release date and
has `∑_j w_j C_j ≤ K`, where `C_j = f j + 1`. -/
def RobotFlowShopThreeMachinesUnitReleaseCompletionFeasible
    (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∃ a b c e f, IsRobotSchedule i a b c e f ∧ (∀ j, releaseDate i j ≤ a j) ∧
    ∑ j, (i.1.get j).2.2.2 * (f j + 1) ≤ i.2

open Classical in
/-- `F3;R1|p_ij=1;t_ik;r_i|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def robotFlowShopThreeMachinesUnitReleaseCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopThreeMachinesUnitReleaseCompletionFeasible i)
  | none => false

/-- **ROBOT FLOW SHOP, TOTAL COMPLETION TIME WITH RELEASE DATES `F3;R1|p_ij=1;t_ik;r_i|ΣC_i` is
NP-complete.** Source: Knust (1999), as recorded by Brucker and Knust; Hurink and Knust (2001)
for the model. -/
public theorem_wanted robotFlowShopThreeMachinesUnitReleaseCompletion_npComplete :
    robotFlowShopThreeMachinesUnitReleaseCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopThreeMachinesUnitReleaseCompletionDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesUnitReleaseCompletion

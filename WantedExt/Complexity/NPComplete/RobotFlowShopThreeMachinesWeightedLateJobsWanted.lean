/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, WEIGHTED NUMBER OF LATE JOBS `F3;R1|p_ij=1;t_ik|Σw_iU_i` is NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik|Σw_iU_i` (minimal NP-hard in the
ordinary sense, citing Knust 1999);
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (the robot model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedLateJobs

open RobotFlowShopThreeMachinesWeightedTardiness
  (RobotFlowShopThreeMachinesWeightedTardinessInstance IsRobotSchedule)

/-!
# ROBOT FLOW SHOP, WEIGHTED NUMBER OF LATE JOBS `F3;R1|p_ij=1;t_ik|Σw_iU_i` is NP-complete

INSTANCE: machines `M_1, M_2, M_3` in a flow shop; jobs `1, …, n`, job `i` consisting of operations
`O_i1, O_i2, O_i3` of unit length (`p_ij = 1`), `O_ij` processed on `M_j`; each machine processes at
most one operation at a time; between `M_k` and `M_(k+1)` (`k = 1, 2`) job `i` is carried by a
single transport robot, the transport taking `t_ik ∈ ℤ₀⁺` time units; the robot carries at most one
job at a time; job `i` has a due date `d_i` and a weight `w_i` (in `ℤ₀⁺`); and a bound `K ∈ ℤ₀⁺`.
QUESTION: is there a feasible schedule in which the late jobs (`C_i > d_i`, where `C_i` is the
completion time of `O_i3`) have total weight at most `K`?

The robot model is that of Hurink and Knust (Section 1): one robot, one job at a time, empty moves
taking no time, unlimited buffers. Brucker and Knust record `F3;R1|p_ij=1;t_ik|Σw_iU_i` as minimal
NP-hard in the ordinary sense, credited to Knust's thesis (1999), which was not available. Numbers
use the binary encoding.

Encoding. The instance (jobs listed one per entry as `(t_i1, t_i2, d_i, w_i)`, the bound `K`)
and the schedules (`IsRobotSchedule`: start times `a, c, f` of the operations and `b, e` of the
transports, each job's steps in order, pairwise different start times on each machine, pairwise
disjoint transport intervals; `C_i = f i + 1`) are those of `F3;R1|p_ij=1;t_ik|Σw_iT_i`
(`RobotFlowShopThreeMachinesWeightedTardinessWanted`); only the question differs. Membership in
NP is that module's certificate argument.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some schedule has late jobs (`d_j < f j + 1`) of total weight at most `K`. -/
def RobotFlowShopThreeMachinesWeightedLateJobsFeasible
    (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∃ a b c e f, IsRobotSchedule i a b c e f ∧
    ∑ j ∈ Finset.univ.filter (fun j => (i.1.get j).2.2.1 < f j + 1), (i.1.get j).2.2.2 ≤
      i.2

open Classical in
/-- `F3;R1|p_ij=1;t_ik|Σw_iU_i` as a decision problem over bitstrings; every decoded instance is
well formed. -/
noncomputable def robotFlowShopThreeMachinesWeightedLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesWeightedTardinessInstance) x with
  | some i => decide (RobotFlowShopThreeMachinesWeightedLateJobsFeasible i)
  | none => false

/-- **ROBOT FLOW SHOP, WEIGHTED NUMBER OF LATE JOBS `F3;R1|p_ij=1;t_ik|Σw_iU_i` is
NP-complete.** Source: Knust (1999), as recorded by Brucker and Knust; Hurink and Knust (2001)
for the model. -/
public theorem_wanted robotFlowShopThreeMachinesWeightedLateJobs_npComplete :
    robotFlowShopThreeMachinesWeightedLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopThreeMachinesWeightedLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedLateJobs

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, TOTAL TARDINESS `F3;R1|p_ij=1;t_ik|ΣT_i` is NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik|ΣT_i` (minimal NP-hard in the
ordinary sense, citing Knust 1999);
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

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesTotalTardiness

open RobotFlowShopThreeMachinesWeightedTardiness
  (RobotFlowShopThreeMachinesWeightedTardinessInstance
    RobotFlowShopThreeMachinesWeightedTardinessFeasible)

/-!
# ROBOT FLOW SHOP, TOTAL TARDINESS `F3;R1|p_ij=1;t_ik|ΣT_i` is NP-complete

INSTANCE: machines `M_1, M_2, M_3` in a flow shop; jobs `1, …, n`, job `i` consisting of operations
`O_i1, O_i2, O_i3` of unit length (`p_ij = 1`), `O_ij` processed on `M_j`; each machine processes at
most one operation at a time; between `M_k` and `M_(k+1)` (`k = 1, 2`) job `i` is carried by a
single transport robot, the transport taking `t_ik ∈ ℤ₀⁺` time units; the robot carries at most one
job at a time; job `i` has a due date `d_i`; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a feasible
schedule with total tardiness `∑_i max(0, C_i - d_i) ≤ K`, where `C_i` is the completion time of
`O_i3`?

The robot model is that of Hurink and Knust (Section 1): one robot, one job at a time, empty moves
taking no time, unlimited buffers. Brucker and Knust record `F3;R1|p_ij=1;t_ik|ΣT_i` as minimal
NP-hard in the ordinary sense, credited to Knust's thesis (1999), which was not available. Numbers
use the binary encoding.

Encoding. This is `F3;R1|p_ij=1;t_ik|Σw_iT_i`
(`RobotFlowShopThreeMachinesWeightedTardinessWanted`) with every weight `w_i = 1`: its instance
(jobs listed one per entry as `(t_i1, t_i2, d_i, w_i)`, the bound `K`), schedules
(`IsRobotSchedule`) and question are reused, and well-formedness asks for unit weights.
Membership in NP is that module's certificate argument.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: every job has weight `1`. -/
def WellFormed (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∀ x ∈ i.1, x.2.2.2 = 1

open Classical in
/-- `F3;R1|p_ij=1;t_ik|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def robotFlowShopThreeMachinesTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopThreeMachinesWeightedTardinessFeasible i)
  | none => false

/-- **ROBOT FLOW SHOP, TOTAL TARDINESS `F3;R1|p_ij=1;t_ik|ΣT_i` is NP-complete.** Source: Knust
(1999), as recorded by Brucker and Knust; Hurink and Knust (2001) for the model. -/
public theorem_wanted robotFlowShopThreeMachinesTotalTardiness_npComplete :
    robotFlowShopThreeMachinesTotalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopThreeMachinesTotalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesTotalTardiness

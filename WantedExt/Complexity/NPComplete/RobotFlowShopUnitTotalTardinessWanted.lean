/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=1;t_i|ΣT_i (two-machine unit flow shop, single transport robot, total tardiness)
is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_1ro` (flow-shop problems with transportation times and a single robot), Universität
Osnabrück (last update 2004), entry `F2;R1|p_ij=1;t_i|ΣT_i` (minimal NP-hard, ordinary
sense), citing S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität
Osnabrück, Fachbereich Mathematik/Informatik (1999) (the thesis text was not available);
robot model: J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with
transportation times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RobotFlowShopUnitTotalTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitTotalTardiness

open RobotFlowShopUnitWeightedTardiness (IsUnitRobotFlowShopSchedule)

/-!
# F2;R1|p_ij=1;t_i|ΣT_i is NP-complete

INSTANCE: two machines `M₁, M₂` in a flow shop and `n` jobs, each job `j` consisting of an
operation of unit length on `M₁` (`p₁ⱼ = 1`) followed by an operation of unit length on `M₂`
(`p₂ⱼ = 1`), each machine processing at most one operation at a time; between its two
operations job `j` is transported from `M₁` to `M₂` by a single robot, the transport taking
`tⱼ ∈ ℤ₀⁺`; each job `j` has a due date `dⱼ ∈ ℤ₀⁺`; and a bound `K`.
QUESTION: is there a feasible schedule whose total tardiness `Σⱼ max(0, Cⱼ - dⱼ)` is at most
`K`, where `Cⱼ` is the completion time of job `j` on `M₂`?

The schedules are those of F2;R1|p_ij=1;t_i|Σw_iT_i (`IsUnitRobotFlowShopSchedule` of
`RobotFlowShopUnitWeightedTardiness`), whose instances also carry weights. The robot model is
that of Hurink and Knust (2001), Section 1: one robot carries every job from `M₁` to `M₂`, at
most one job at a time, the transport of job `j` taking `tⱼ` time units; empty moves of the
robot take no time; buffers before and after the machines are unlimited. A schedule gives the
start times `σ 0 j`, `σ 1 j` of job `j`'s operations on `M₁`, `M₂` and the start time `ρ j` of
its transport: the machines run a schedule of the unit-time flow shop with transportation delays
`t`, each transport starts after the job's operation on `M₁` and ends by the start of its
operation on `M₂`, and the transports of distinct jobs do not overlap. `Cⱼ = σ 1 j + 1`, and
`Cⱼ - dⱼ` in `ℕ` is `max(0, Cⱼ - dⱼ)`. Start times are natural numbers: with integer data,
starting every operation as early as the order of the operations on `M₁`, on the robot and on
`M₂` allows gives an integral schedule whose completion times are no later, so this does not
change the answer. Every decoded instance is well formed (all data, `K` included, are
non-negative integers). The jobs are `Fin n`, one per listed pair. Binary encoding of all
numbers.

Membership in NP: some optimal schedule starts every operation by `Σⱼ (tⱼ + 2)`, so start
times form a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **F2;R1|p_ij=1;t_i|ΣT_i is NP-complete.**
Source: Brucker and Knust's classification, class `f_1ro`, citing Knust (1999); robot model of
Hurink and Knust (2001). -/
public theorem_wanted robotFlowShopUnitTotalTardiness_npComplete :
    robotFlowShopUnitTotalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopUnitTotalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopUnitTotalTardiness

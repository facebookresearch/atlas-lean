/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, EQUAL PROCESSING TIMES, MAXIMUM LATENESS `F3;R1|p_ij=p;t_ik|L_max` is
# NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=p;t_ik|L_max` (minimal NP-hard in
the strong sense, citing Knust 1999);
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (the robot model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualLateness

open RobotFlowShopThreeMachinesEqualReleaseMakespan (IsEqualRobotSchedule)

/-!
# ROBOT FLOW SHOP, EQUAL PROCESSING TIMES, MAXIMUM LATENESS `F3;R1|p_ij=p;t_ik|L_max`

INSTANCE: machines `M_1, M_2, M_3` in a flow shop; jobs `1, …, n`, job `i` consisting of
operations `O_i1, O_i2, O_i3` of equal length `p` (`p_ij = p`, `p ∈ ℤ⁺` part of the input),
`O_ij` processed on `M_j`; each machine processes at most one operation at a time; between `M_k`
and `M_(k+1)` (`k = 1, 2`) job `i` is carried by a single transport robot, the transport taking
`t_ik ∈ ℤ₀⁺` time units; the robot carries at most one job at a time; job `i` has a due date
`d_i ∈ ℤ₀⁺`; and an integer `y`. QUESTION: is there a feasible schedule whose maximum lateness
`L_max = max_i (C_i - d_i)` is at most `y`, where `C_i` is the completion time of `O_i3`?

This is `F3;R1|p_ij=p;t_ik|L_max` in the notation of the Brucker-Knust classification, which
records it as minimal NP-hard in the strong sense, credited to Knust's thesis (1999), which was
not available. The robot model is that of Hurink and Knust (Section 1): one robot transports
every job between consecutive machines, handles one job at a time, its empty moves take no time,
and buffers are unlimited.

Encoding. The schedules are those of `F3;R1|p_ij=p;t_ik;r_i|C_max`
(`IsEqualRobotSchedule` of `RobotFlowShopThreeMachinesEqualReleaseMakespanWanted`), without
release dates. Jobs are listed one per entry as `(t_i1, t_i2, d_i)`; jobs are `Fin n`. A
schedule gives job `i` start times `a i`, `c i`, `f i` of its operations on `M_1`, `M_2`, `M_3`
and start times `b i`, `e i` of its two transports: a job's steps follow each other
(`a i + p ≤ b i`, `b i + t_i1 ≤ c i`, `c i + p ≤ e i`, `e i + t_i2 ≤ f i`), the operations on each
machine occupy pairwise disjoint sets of time units, and so do the `2n` transports.
`C_i = f i + p`. The bound `y` is an integer, encoded as a pair `(y⁺, y⁻)` of naturals
representing `y⁺ - y⁻`, as in `RobotFlowShopUnitReleaseLatenessWanted`
(`F2;R1|p_ij=1;t_i;r_i|L_max`); `C_i - d_i ≤ y⁺ - y⁻` is stated over `ℕ` as
`C_i + y⁻ ≤ d_i + y⁺`. Well-formedness asks for `p > 0` and at least one job, so that `L_max`
is a maximum over a nonempty set. With integer data, integer start times lose no generality.
Membership in NP: some optimal schedule starts every step by `∑_i (3p + t_i1 + t_i2)`, so start
times form a certificate of polynomial size. Binary encoding of all numbers (the problem is
NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ROBOT FLOW SHOP, EQUAL PROCESSING TIMES, MAXIMUM LATENESS `F3;R1|p_ij=p;t_ik|L_max` is
NP-complete.** Source: Knust (1999), as recorded by Brucker and Knust; Hurink and Knust (2001)
for the model. -/
public theorem_wanted robotFlowShopThreeMachinesEqualLateness_npComplete :
    robotFlowShopThreeMachinesEqualLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopThreeMachinesEqualLatenessDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualLateness

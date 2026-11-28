/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|p_ij=p;t_j|C_max (two-machine flow shop, single transport robot, equal processing times) is
NP-complete

Source:
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (Theorem 2: strongly NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RobotFlowShopEqualProcessingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopEqualProcessing

/-!
# F2;R1|p_ij=p;t_j|C_max is NP-complete

INSTANCE: two machines `M₁, M₂` in a flow shop and jobs `j`, each consisting of an operation on
`M₁` followed by an operation on `M₂`, all operations of the same length `p ∈ ℤ₀⁺`, each machine
processing at most one operation at a time; between its two operations each job `j` is
transported from `M₁` to `M₂` by a single robot, taking `tⱼ ∈ ℤ₀⁺` time units; and a bound `K`.
QUESTION: is there a feasible schedule with makespan `max_j Cⱼ ≤ K`?

The robot model is that of Hurink and Knust (2001): one robot carries every job from `M₁` to
`M₂`, at most one job at a time, the transport of job `j` taking `tⱼ` time units; empty moves of
the robot take no time; buffers before and after the machines are unlimited. As Hurink and Knust
note (Section 2), `F2;R1|tⱼ|C_max` is then the three-machine flow shop `F3||C_max` in which the
second machine is the robot: a job is transported after its operation on `M₁` and processed on
`M₂` after its transport, and the robot, like a machine, handles one job at a time. The question
is therefore stated through FLOW-SHOP SCHEDULING ([SS15], `FlowShopSchedulingWanted`): `toFlowShop`
builds the instance with `m = 3` processors `M₁`, robot, `M₂`, job `j` given the task lengths
`[p₁ⱼ, tⱼ, p₂ⱼ]`, and deadline `D = K`; the makespan is at most `K` iff every task (in
particular each job's last) ends by `D`. Every decoded instance is well formed (all data, `K`
included, are non-negative integers; `m = 3` and three tasks per job hold by construction).
Here `p₁ⱼ = p₂ⱼ = p` for every job. Hurink and Knust distinguish `pᵢⱼ = p`
(integer data, strongly NP-hard) from `pᵢⱼ = 1` (polynomial); the instance carries the integer
`p`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **F2;R1|p_ij=p;t_j|C_max is NP-complete.**
Source: Hurink and Knust (2001), Theorem 2. -/
public theorem_wanted robotFlowShopEqualProcessing_npComplete :
    robotFlowShopEqualProcessingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopEqualProcessingDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopEqualProcessing

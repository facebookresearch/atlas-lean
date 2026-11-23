/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2;R1|t_j=T|C_max (two-machine flow shop, single transport robot, constant transport times) is
NP-complete

Source:
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (Theorem 1: strongly NP-hard);
H. Kise, "On an automated two-machine flowshop scheduling problem with infinite buffer",
Journal of the Operations Research Society of Japan 34(3) (1991), 354-361,
doi:10.15807/jorsj.34.354 (NP-hard in the ordinary sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FlowShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopConstantTransport

/-!
# F2;R1|t_j=T|C_max is NP-complete

INSTANCE: two machines `M₁, M₂` in a flow shop and jobs `j`, each consisting of an operation of
length `p₁ⱼ ∈ ℤ₀⁺` on `M₁` followed by an operation of length `p₂ⱼ ∈ ℤ₀⁺` on `M₂`, each machine
processing at most one operation at a time; between its two operations each job is transported
from `M₁` to `M₂` by a single robot, and every transport takes the same time `T ∈ ℤ₀⁺`; and a
bound `K`.
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
Here `tⱼ = T` for every job. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs `(p₁ⱼ, p₂ⱼ)`, the transport time `T`, and the bound `K`. -/
abbrev RobotFlowShopConstantTransportInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- The three-machine flow shop `M₁`, robot, `M₂`: job `j` has task lengths `[p₁ⱼ, T, p₂ⱼ]`,
and the deadline is `K`. -/
def toFlowShop (i : RobotFlowShopConstantTransportInstance) :
    FlowShopScheduling.FlowShopSchedulingInstance :=
  (3, i.1.map (fun q => [q.1, i.2.1, q.2]), i.2.2)

/-- Well-formedness: every instance (all data are non-negative integers). -/
def WellFormed (_ : RobotFlowShopConstantTransportInstance) : Prop := True

/-- Some schedule of `M₁`, the robot and `M₂` (a flow-shop schedule of `toFlowShop i`) has
makespan at most `K`. -/
def RobotFlowShopConstantTransportFeasible (i : RobotFlowShopConstantTransportInstance) :
    Prop :=
  FlowShopScheduling.FlowShopSchedulingFeasible (toFlowShop i)

open Classical in
/-- F2;R1|t_j=T|C_max as a decision
problem over bitstrings. -/
noncomputable def robotFlowShopConstantTransportDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopConstantTransportInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopConstantTransportFeasible i)
  | none => false

/-- **F2;R1|t_j=T|C_max is NP-complete.**
Source: Hurink and Knust (2001), Theorem 1; Kise (1991). -/
public theorem_wanted robotFlowShopConstantTransport_npComplete :
    robotFlowShopConstantTransportDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopConstantTransportDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopConstantTransport

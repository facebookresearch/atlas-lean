/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, TOTAL WEIGHTED TARDINESS `F3;R1|p_ij=1;t_ik|Σw_iT_i` is NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=1;t_ik|Σw_iT_i` (minimal NP-hard in
the strong sense, citing Knust 1999);
J. Hurink and S. Knust, "Makespan minimization for flow-shop problems with transportation
times and a single robot", Discrete Applied Mathematics 112 (2001), 199-216,
doi:10.1016/S0166-218X(00)00316-4 (the robot model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedTardiness

/-!
# ROBOT FLOW SHOP, TOTAL WEIGHTED TARDINESS `F3;R1|p_ij=1;t_ik|Σw_iT_i` is NP-complete

INSTANCE: machines `M_1, M_2, M_3` in a flow shop; jobs `1, …, n`, job `i` consisting of
operations `O_i1, O_i2, O_i3` of unit length (`p_ij = 1`), `O_ij` processed on `M_j`; each
machine processes at most one operation at a time; between `M_k` and `M_(k+1)` (`k = 1, 2`) job
`i` is carried by a single transport robot, the transport taking `t_ik ∈ ℤ₀⁺` time units; the
robot carries at most one job at a time; job `i` has a due date `d_i` and a weight `w_i` (in
`ℤ₀⁺`); and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a feasible schedule with total weighted
tardiness `∑_i w_i max(0, C_i - d_i) ≤ K`, where `C_i` is the completion time of `O_i3`?

The robot model is that of Hurink and Knust (Section 1): a single robot transports every job
between consecutive machines, handles one job at a time, its empty moves take no time ("empty
moving times of the robot are negligible"), and buffers are unlimited. Brucker and Knust record
`F3;R1|p_ij=1;t_ik|Σw_iT_i` as minimal NP-hard in the strong sense, credited to Knust's thesis
(1999), which was not available.

Encoding. Jobs are listed one per entry as `(t_i1, t_i2, d_i, w_i)`; jobs are `Fin n`. A schedule
gives job `i` start times `a i`, `c i`, `f i` of its operations on `M_1`, `M_2`, `M_3` and start
times `b i`, `e i` of its two transports. A job's steps follow each other: `a i + 1 ≤ b i`,
`b i + t_i1 ≤ c i`, `c i + 1 ≤ e i`, `e i + t_i2 ≤ f i`. With unit operations a machine processes
one operation at a time exactly when its start times are pairwise different. The `2n` transports
occupy pairwise disjoint sets of time units `[b i, b i + t_i1)` and `[e i, e i + t_i2)`
(`Finset.Ico`; a transport of length `0` occupies none). `C_i = f i + 1`. With integer data, integer
start times lose no generality. Membership in NP is the certificate argument: shifting steps earlier
while the schedule stays feasible increases no completion time, so every start time can be taken at
most `∑_i (3 + t_i1 + t_i2)`, and the start times are checked in polynomial time. Binary encoding of
all numbers (the problem is NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs `(t_i1, t_i2, d_i, w_i)` (transport times from `M_1` to `M_2` and from
`M_2` to `M_3`, due date, weight), one per entry, and the bound `K`. -/
abbrev RobotFlowShopThreeMachinesWeightedTardinessInstance := List (ℕ × ℕ × ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Type := Fin i.1.length

/-- Start times `a`, `c`, `f` (operations on `M_1`, `M_2`, `M_3`) and `b`, `e` (transports
`M_1 → M_2`, `M_2 → M_3`) form a schedule: each job's steps in order, pairwise different start
times on each machine (unit operations), and pairwise disjoint sets of time units occupied by
the transports. -/
def IsRobotSchedule (i : RobotFlowShopThreeMachinesWeightedTardinessInstance)
    (a b c e f : Job i → ℕ) : Prop :=
  (∀ j, a j + 1 ≤ b j ∧ b j + (i.1.get j).1 ≤ c j ∧ c j + 1 ≤ e j ∧
      e j + (i.1.get j).2.1 ≤ f j) ∧
    Function.Injective a ∧ Function.Injective c ∧ Function.Injective f ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (b j) (b j + (i.1.get j).1))
      (Finset.Ico (b j') (b j' + (i.1.get j').1))) ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (e j) (e j + (i.1.get j).2.1))
      (Finset.Ico (e j') (e j' + (i.1.get j').2.1))) ∧
    ∀ j j', Disjoint (Finset.Ico (b j) (b j + (i.1.get j).1))
      (Finset.Ico (e j') (e j' + (i.1.get j').2.1))

/-- Some schedule has total weighted tardiness `∑_j w_j (f j + 1 - d_j)` at most `K` (natural
subtraction: the tardiness `max(0, C_j - d_j)`). -/
def RobotFlowShopThreeMachinesWeightedTardinessFeasible
    (i : RobotFlowShopThreeMachinesWeightedTardinessInstance) : Prop :=
  ∃ a b c e f, IsRobotSchedule i a b c e f ∧
    ∑ j, (i.1.get j).2.2.2 * (f j + 1 - (i.1.get j).2.2.1) ≤ i.2

open Classical in
/-- `F3;R1|p_ij=1;t_ik|Σw_iT_i` as a decision problem over bitstrings; every decoded instance is
well formed. -/
noncomputable def robotFlowShopThreeMachinesWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesWeightedTardinessInstance) x with
  | some i => decide (RobotFlowShopThreeMachinesWeightedTardinessFeasible i)
  | none => false

/-- **ROBOT FLOW SHOP, TOTAL WEIGHTED TARDINESS `F3;R1|p_ij=1;t_ik|Σw_iT_i` is NP-complete.**
Source: Knust (1999), as recorded by Brucker and Knust; Hurink and Knust (2001) for the
model. -/
public theorem_wanted robotFlowShopThreeMachinesWeightedTardiness_npComplete :
    robotFlowShopThreeMachinesWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopThreeMachinesWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesWeightedTardiness

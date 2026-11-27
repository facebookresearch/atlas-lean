/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROBOT FLOW SHOP, EQUAL PROCESSING TIMES, MAKESPAN WITH RELEASE DATES
# `F3;R1|p_ij=p;t_ik;r_i|C_max` is NP-complete

Source:
S. Knust, *Shop-scheduling problems with transportation*, PhD thesis, Universität Osnabrück
(1999) (not available; the result is recorded by Brucker and Knust);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `f_1ro` (flow-shop problems with
transportation times and a single robot), entry `F3;R1|p_ij=p;t_ik;r_i|C_max` (minimal NP-hard
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
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualReleaseMakespan

/-!
# ROBOT FLOW SHOP, EQUAL PROCESSING TIMES, MAKESPAN WITH RELEASE DATES

INSTANCE: machines `M_1, M_2, M_3` in a flow shop; jobs `1, …, n`, job `i` consisting of
operations `O_i1, O_i2, O_i3` of equal length `p` (`p_ij = p`, `p ∈ ℤ⁺` part of the input),
`O_ij` processed on `M_j`; each machine processes at most one operation at a time; between `M_k`
and `M_(k+1)` (`k = 1, 2`) job `i` is carried by a single transport robot, the transport taking
`t_ik ∈ ℤ₀⁺` time units; the robot carries at most one job at a time; job `i` has a release date
`r_i ∈ ℤ₀⁺`, before which it cannot start; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a feasible
schedule with makespan `max_i C_i ≤ K`, where `C_i` is the completion time of `O_i3`?

This is `F3;R1|p_ij=p;t_ik;r_i|C_max` in the notation of the Brucker-Knust classification, which
records it as minimal NP-hard in the strong sense, credited to Knust's thesis (1999), which was
not available. The robot model is that of Hurink and Knust (Section 1): one robot transports
every job between consecutive machines, handles one job at a time, its empty moves take no time
("empty moving times of the robot are negligible"), and buffers are unlimited.

Encoding. Jobs are listed one per entry as `(t_i1, t_i2, r_i)`; jobs are `Fin n`. A schedule
(`IsEqualRobotSchedule`) gives job `i` start times `a i`, `c i`, `f i` of its operations on
`M_1`, `M_2`, `M_3` and start times `b i`, `e i` of its two transports. A job's steps follow each
other: `a i + p ≤ b i`, `b i + t_i1 ≤ c i`, `c i + p ≤ e i`, `e i + t_i2 ≤ f i`. The operations of
different jobs on one machine occupy pairwise disjoint sets of time units `[a i, a i + p)` (resp.
with `c`, `f`), and the `2n` transports occupy pairwise disjoint sets of time units
`[b i, b i + t_i1)` and `[e i, e i + t_i2)` (`Finset.Ico`; a transport of length `0` occupies
none). These are the conditions of `IsRobotSchedule` of
`RobotFlowShopThreeMachinesWeightedTardinessWanted` (`F3;R1|p_ij=1;t_ik|Σw_iT_i`), whose unit
operations make the machine conditions injectivity of start times; with operations of length
`p` they are interval disjointness, so the predicate is stated here for every `p`, over job
sets `Fin n` and the two transport-time functions. Job `i` starts on `M_1` no earlier than `r_i`,
and `C_i = f i + p`. With integer data, starting every step as early as the release dates and
the orders on the machines and on the robot allow gives an integral schedule with no later
completion times, so integer start times lose no generality. Membership in NP: some optimal
schedule starts every step by `max_i r_i + ∑_i (3p + t_i1 + t_i2)`, so start times form a
certificate of polynomial size. Well-formedness asks for at least one job, so that `C_max` is a
maximum over a nonempty set, and `p > 0`. Binary encoding of all numbers (the problem is NP-hard
in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Start times `a`, `c`, `f` (operations on `M_1`, `M_2`, `M_3`, each of length `p`) and `b`,
`e` (transports `M_1 → M_2` and `M_2 → M_3` of job `j`, of lengths `t₁ j` and `t₂ j`) form a
single-robot flow-shop schedule of the jobs `Fin n`: each job's steps in order, pairwise
disjoint sets of time units occupied by the operations on each machine, and pairwise disjoint
sets of time units occupied by the transports. -/
def IsEqualRobotSchedule (p : ℕ) {n : ℕ} (t₁ t₂ : Fin n → ℕ) (a b c e f : Fin n → ℕ) : Prop :=
  (∀ j, a j + p ≤ b j ∧ b j + t₁ j ≤ c j ∧ c j + p ≤ e j ∧ e j + t₂ j ≤ f j) ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (a j) (a j + p)) (Finset.Ico (a j') (a j' + p))) ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (c j) (c j + p)) (Finset.Ico (c j') (c j' + p))) ∧
    (∀ j j', j ≠ j' → Disjoint (Finset.Ico (f j) (f j + p)) (Finset.Ico (f j') (f j' + p))) ∧
    (∀ j j', j ≠ j' →
      Disjoint (Finset.Ico (b j) (b j + t₁ j)) (Finset.Ico (b j') (b j' + t₁ j'))) ∧
    (∀ j j', j ≠ j' →
      Disjoint (Finset.Ico (e j) (e j + t₂ j)) (Finset.Ico (e j') (e j' + t₂ j'))) ∧
    ∀ j j', Disjoint (Finset.Ico (b j) (b j + t₁ j)) (Finset.Ico (e j') (e j' + t₂ j'))

/-- An instance: the jobs `(t_i1, t_i2, r_i)` (transport times from `M_1` to `M_2` and from `M_2`
to `M_3`, release date), one per entry, the processing time `p` and the bound `K`. -/
abbrev RobotFlowShopThreeMachinesEqualReleaseMakespanInstance := List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) : Type := Fin i.1.length

/-- The transport time `t_i1` of job `i` from `M_1` to `M_2`. -/
def firstTransport (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) (j : Job i) :
    ℕ :=
  (i.1.get j).1

/-- The transport time `t_i2` of job `i` from `M_2` to `M_3`. -/
def secondTransport (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) (j : Job i) :
    ℕ :=
  (i.1.get j).2.1

/-- The release date `r_i` of job `i`. -/
def releaseDate (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Well-formedness: there is at least one job, so that `C_max` is a maximum over a nonempty set,
and the processing time `p` is positive. -/
def WellFormed (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) : Prop :=
  i.1 ≠ [] ∧ 0 < i.2.1

/-- Some single-robot schedule with operations of length `p` starts every job on `M_1` no earlier
than its release date and completes every job by `K` (`C_j = f j + p`). -/
def RobotFlowShopThreeMachinesEqualReleaseMakespanFeasible
    (i : RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) : Prop :=
  ∃ a b c e f, IsEqualRobotSchedule i.2.1 (firstTransport i) (secondTransport i) a b c e f ∧
    (∀ j, releaseDate i j ≤ a j) ∧ ∀ j, f j + i.2.1 ≤ i.2.2

open Classical in
/-- `F3;R1|p_ij=p;t_ik;r_i|C_max` as a decision problem over bitstrings. -/
noncomputable def robotFlowShopThreeMachinesEqualReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RobotFlowShopThreeMachinesEqualReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ RobotFlowShopThreeMachinesEqualReleaseMakespanFeasible i)
  | none => false

/-- **ROBOT FLOW SHOP, EQUAL PROCESSING TIMES, MAKESPAN WITH RELEASE DATES
`F3;R1|p_ij=p;t_ik;r_i|C_max` is NP-complete.** Source: Knust (1999), as recorded by Brucker
and Knust; Hurink and Knust (2001) for the model. -/
public theorem_wanted robotFlowShopThreeMachinesEqualReleaseMakespan_npComplete :
    robotFlowShopThreeMachinesEqualReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L robotFlowShopThreeMachinesEqualReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.RobotFlowShopThreeMachinesEqualReleaseMakespan

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COUPLED-TASK SCHEDULING is NP-complete

Source:
A. J. Orman and C. N. Potts, "On the complexity of coupled-task scheduling", Discrete Applied
Mathematics 72 (1997), 141-154, doi:10.1016/S0166-218X(96)00041-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoupledTaskScheduling

/-!
# COUPLED-TASK SCHEDULING is NP-complete

The problem `1 | (a_j, L_j, b_j) | C_max` of Orman and Potts (1997). A coupled-task job `j`
consists of two operations that must be processed on a single machine in a fixed order: a
first operation of length `a_j`, and a second operation of length `b_j` that starts exactly
`L_j` time units after the first one completes. The machine processes at most one operation at
a time; operations of other jobs may be processed during the delay `L_j`. Given a bound `K`,
the question is whether there is a schedule of all jobs with makespan at most `K`.

Operation lengths `a_j`, `b_j` are positive integers and delays `L_j` are nonnegative
integers, all in binary encoding. Orman and Potts prove the problem strongly NP-hard, already
for special cases in which two of the three parameters are common to all jobs; NP membership
holds because start times bounded by `K` form a polynomial-size certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs as triples `(a_j, L_j, b_j)` (first operation length, exact delay,
second operation length) and the makespan bound `K`. -/
abbrev CoupledTaskSchedulingInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every operation length `a_j`, `b_j` is positive. -/
def WellFormed (i : CoupledTaskSchedulingInstance) : Prop :=
  ∀ t ∈ i.1, 0 < t.1 ∧ 0 < t.2.2

/-- The two operations of job `t = (a, L, b)` started at time `s`, as half-open time intervals
`[start, finish)`: the first operation occupies `[s, s + a)` and the second
`[s + a + L, s + a + L + b)`. -/
def operations (t : ℕ × ℕ × ℕ) (s : ℕ) : List (ℕ × ℕ) :=
  [(s, s + t.1), (s + t.1 + t.2.1, s + t.1 + t.2.1 + t.2.2)]

/-- There are start times `s j` such that every job completes by `K` and no two operations of
different jobs overlap on the machine. (The two operations of one job never overlap, since
`L_j ≥ 0`.) -/
def CoupledTaskSchedulingFeasible (i : CoupledTaskSchedulingInstance) : Prop :=
  ∃ s : Fin i.1.length → ℕ,
    (∀ j, s j + (i.1.get j).1 + (i.1.get j).2.1 + (i.1.get j).2.2 ≤ i.2) ∧
    ∀ j k, j ≠ k → ∀ I ∈ operations (i.1.get j) (s j), ∀ J ∈ operations (i.1.get k) (s k),
      I.2 ≤ J.1 ∨ J.2 ≤ I.1

open Classical in
/-- COUPLED-TASK SCHEDULING as a decision problem over bitstrings. -/
noncomputable def coupledTaskSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoupledTaskSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ CoupledTaskSchedulingFeasible i)
  | none => false

/-- **COUPLED-TASK SCHEDULING is NP-complete.** Source: Orman and Potts (1997). -/
public theorem_wanted coupledTaskScheduling_npComplete :
    coupledTaskSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coupledTaskSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.CoupledTaskScheduling

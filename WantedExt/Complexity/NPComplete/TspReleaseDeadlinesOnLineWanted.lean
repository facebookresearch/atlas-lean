/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TSP WITH RELEASE TIMES AND DEADLINES ON A LINE is NP-complete

Source:
J. N. Tsitsiklis, "Special cases of traveling salesman and repairman problems with time
windows", Networks 22(3) (1992), 263-282, doi:10.1002/net.3230220305, Theorem 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TspReleaseDeadlinesOnLine

/-!
# TSP WITH RELEASE TIMES AND DEADLINES ON A LINE is NP-complete

INSTANCE: a starting point `x*` and `n ≥ 1` jobs on the line, job `i` at the integer location
`x_i` with a release time `r_i` and a deadline `d_i`.
QUESTION: can a server that starts at `x*` at time `0` and moves at unit speed (or stays in
place) execute every job `i` at some time `t_i ∈ [r_i, d_i]`?

This is Tsitsiklis's Line-TSPTW with zero processing times: the distance between locations is
`|x_i - x_j|`, and a feasible schedule is an order `π` of the jobs with nonnegative integer
times `t_i` such that (a) `r_i ≤ t_i ≤ d_i`, (b) `|x* - x_{π(1)}| ≤ t_{π(1)}`, and (c)
`t_{π(k)} + |x_{π(k)} - x_{π(k+1)}| ≤ t_{π(k+1)}`. Theorem 2 shows that testing feasibility is
strongly NP-complete, even when the processing times are zero. Translating all locations by
the same amount changes no distance, so locations are given as natural numbers. Deadlines are
natural numbers; the source also allows `d_i = ∞`, which changes no answer when replaced by
`max_j r_j + n · W`, `W` the largest distance between two of the points `x*, x_1, …, x_n`,
because a feasible order stays feasible when every job is executed as early as possible.
The order is a permutation of `List.range n`; distances are Mathlib's `Nat.dist`.

The model differs from `TspTimeWindowsFeasibilityWanted` (Savelsbergh's path from an origin
vertex to a destination vertex): here the server starts at a point that carries no job, ends
anywhere, and several jobs may share a location.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the starting point `x*`, and the jobs as `(x_i, r_i, d_i)`. -/
abbrev TspReleaseDeadlinesOnLineInstance := ℕ × List (ℕ × ℕ × ℕ)

/-- The number of jobs. -/
abbrev numJobs (i : TspReleaseDeadlinesOnLineInstance) : ℕ := i.2.length

/-- The location `x_a` of job `a`. -/
def location (i : TspReleaseDeadlinesOnLineInstance) (a : ℕ) : ℕ := (i.2.getD a (0, 0, 0)).1

/-- The release time `r_a` of job `a`. -/
def release (i : TspReleaseDeadlinesOnLineInstance) (a : ℕ) : ℕ := (i.2.getD a (0, 0, 0)).2.1

/-- The deadline `d_a` of job `a`. -/
def deadline (i : TspReleaseDeadlinesOnLineInstance) (a : ℕ) : ℕ := (i.2.getD a (0, 0, 0)).2.2

/-- Well-formedness of an instance: there is at least one job. -/
def WellFormed (i : TspReleaseDeadlinesOnLineInstance) : Prop := 0 < numJobs i

/-- A feasible schedule exists: an order of the jobs and times `t` with every `t_a` in the
window of job `a`, the first job reachable from `x*` by its time, and each next job reachable
from the previous one in the time between them. -/
def TspReleaseDeadlinesOnLineFeasible (i : TspReleaseDeadlinesOnLineInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range (numJobs i)) ∧
    ∃ t : ℕ → ℕ, (∀ a < numJobs i, release i a ≤ t a ∧ t a ≤ deadline i a) ∧
      (∀ a ∈ order.head?, Nat.dist i.1 (location i a) ≤ t a) ∧
      ∀ p ∈ order.zip order.tail, t p.1 + Nat.dist (location i p.1) (location i p.2) ≤ t p.2

open Classical in
/-- TSP WITH RELEASE TIMES AND DEADLINES ON A LINE as a decision problem over bitstrings. -/
noncomputable def tspReleaseDeadlinesOnLineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TspReleaseDeadlinesOnLineInstance) x with
  | some i => decide (WellFormed i ∧ TspReleaseDeadlinesOnLineFeasible i)
  | none => false

/-- **TSP WITH RELEASE TIMES AND DEADLINES ON A LINE is NP-complete.** Source: Tsitsiklis
(1992), Theorem 2. -/
public theorem_wanted tspReleaseDeadlinesOnLine_npComplete :
    tspReleaseDeadlinesOnLineDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tspReleaseDeadlinesOnLineDec

end MetaMathlibExt.Complexity.NPComplete.TspReleaseDeadlinesOnLine

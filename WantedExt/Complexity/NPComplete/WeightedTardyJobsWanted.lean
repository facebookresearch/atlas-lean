/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED NUMBER OF TARDY JOBS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), WEIGHTED NUMBER OF TARDY
JOBS (1||sum w_j U_j).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs

/-!
# WEIGHTED NUMBER OF TARDY JOBS is NP-complete

Jobs with processing times, due dates, and weights, and a bound `K`. The question is whether
some ordering has weighted number of tardy jobs at most `K`: a job is tardy if it completes
after its due date, and contributes its weight when tardy, computed by a fold over the
ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A weighted-tardy-jobs instance: jobs (processing time, due date, weight), bound. -/
abbrev WeightedTardyJobsInstance := List (ℕ × ℕ × ℕ) × ℕ


/-- One job's effect on (elapsed time, weighted tardy sum). -/
def WeightedTardyStep (jobs : List (ℕ × ℕ × ℕ)) (state : ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  let t := state.1 + (jobs.getD j (0, 0, 0)).1
  (t, state.2 + if (jobs.getD j (0, 0, 0)).2.1 < t then (jobs.getD j (0, 0, 0)).2.2 else 0)

/-- Weighted number of tardy jobs for a job order (job indices). -/
def WeightedTardy (jobs : List (ℕ × ℕ × ℕ)) (order : List ℕ) : ℕ :=
  (order.foldl (WeightedTardyStep jobs) (0, 0)).2


/-- An ordering with weighted tardy sum at most `K`. -/
def WeightedTardyJobsFeasible
    (i : WeightedTardyJobsInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range i.1.length) ∧
    WeightedTardy i.1 order ≤ i.2

open Classical in
/-- WEIGHTED NUMBER OF TARDY JOBS as a decision problem over bitstrings. -/
noncomputable def weightedTardyJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedTardyJobsInstance) x with
  | some i => decide (WeightedTardyJobsFeasible i)
  | none => false

/-- **WEIGHTED NUMBER OF TARDY JOBS is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), WEIGHTED NUMBER OF TARDY JOBS (1||sum w_j U_j). -/
public theorem_wanted weightedTardyJobs_npComplete :
    weightedTardyJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedTardyJobsDec

end MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs

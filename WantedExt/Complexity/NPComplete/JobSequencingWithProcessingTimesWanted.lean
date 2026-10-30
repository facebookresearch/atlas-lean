/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB SEQUENCING WITH DEADLINES, PROCESSING TIMES, AND PROFITS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SEQUENCING WITH DEADLINES
AND PROFITS (arbitrary processing times); R. M. Karp, "Reducibility among combinatorial
problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.JobSequencingWithProcessingTimes

/-!
# JOB SEQUENCING WITH DEADLINES, PROCESSING TIMES, AND PROFITS is NP-complete

Jobs with processing times, deadlines, and profits, and a profit bound `K`. The question is
whether jobs can be selected and ordered arbitrarily (the witness is an ordering of job
indices, not the input order), each completing by its deadline, with total profit at least `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A job-sequencing instance: jobs (processing time, deadline, profit), profit bound. -/
abbrev JobSequencingWithProcessingTimesInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- A job ordering meeting all deadlines of profit at least `K`. -/
def JobSequencingWithProcessingTimesFeasible
    (i : JobSequencingWithProcessingTimesInstance) : Prop :=
  ∃ order : List ℕ, order.Nodup ∧ (∀ j ∈ order, j < i.1.length) ∧
    i.2 ≤ (order.map (fun j => (i.1.getD j (0, 0, 0)).2.2)).sum ∧
    ∀ t < order.length,
      ((order.take (t + 1)).map (fun j => (i.1.getD j (0, 0, 0)).1)).sum ≤
        (i.1.getD (order.getD t 0) (0, 0, 0)).2.1

open Classical in
/-- JOB SEQUENCING WITH DEADLINES, PROCESSING TIMES, AND PROFITS as a decision problem over
bitstrings. -/
noncomputable def jobSequencingWithProcessingTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobSequencingWithProcessingTimesInstance) x with
  | some i => decide (JobSequencingWithProcessingTimesFeasible i)
  | none => false

/-- **JOB SEQUENCING WITH DEADLINES, PROCESSING TIMES, AND PROFITS is NP-complete.** Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SEQUENCING WITH
DEADLINES AND PROFITS (arbitrary processing times); R. M. Karp, "Reducibility among
combinatorial problems" (1972). -/
public theorem_wanted jobSequencingWithProcessingTimes_npComplete :
    jobSequencingWithProcessingTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L jobSequencingWithProcessingTimesDec

end MetaMathlibExt.Complexity.NPComplete.JobSequencingWithProcessingTimes

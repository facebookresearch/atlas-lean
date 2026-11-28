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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.JobSequencingWithProcessingTimesDefs

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

/-- **JOB SEQUENCING WITH DEADLINES, PROCESSING TIMES, AND PROFITS is NP-complete.** The decision
problem of job sequencing with deadlines, processing times and profits on bitstrings is
NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one
reduction to it.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SEQUENCING WITH
DEADLINES AND PROFITS (arbitrary processing times); R. M. Karp, "Reducibility among
combinatorial problems" (1972). -/
public theorem_wanted jobSequencingWithProcessingTimes_npComplete :
    jobSequencingWithProcessingTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L jobSequencingWithProcessingTimesDec

end MetaMathlibExt.Complexity.NPComplete.JobSequencingWithProcessingTimes

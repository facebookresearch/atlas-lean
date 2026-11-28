/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL MACHINES WITH DEADLINES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARALLEL MACHINE
SCHEDULING WITH DEADLINES.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ParallelMachinesDeadlinesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelMachinesDeadlines

/-!
# PARALLEL MACHINES WITH DEADLINES is NP-complete

Jobs with processing times and deadlines, and a number `m` of identical parallel machines. The
question is whether there are start times and machine assignments so that every job completes
by its deadline and no machine runs two jobs at once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARALLEL MACHINES WITH DEADLINES is NP-complete.** The PARALLEL MACHINES WITH DEADLINES
decision problem belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), PARALLEL MACHINE SCHEDULING WITH
DEADLINES. -/
public theorem_wanted parallelMachinesDeadlines_npComplete :
    parallelMachinesDeadlinesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L parallelMachinesDeadlinesDec

end MetaMathlibExt.Complexity.NPComplete.ParallelMachinesDeadlines

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL TARDINESS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), TOTAL TARDINESS (1||sum
T_j); J. Du and J. Y.-T. Leung, "Minimizing total tardiness on one machine is NP-hard" (1990).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TotalTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalTardiness

/-!
# TOTAL TARDINESS is NP-complete

Jobs with processing times and due dates, and a bound `K`. The question is whether some
ordering has total tardiness at most `K`, where a job's tardiness is the excess of its
completion time over its due date (zero if on time), computed by a fold over the ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TOTAL TARDINESS is NP-complete.** The TOTAL TARDINESS decision problem belongs to NP, and
every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), TOTAL TARDINESS (1||sum T_j); J. Du and J. Y.-T. Leung,
"Minimizing total tardiness on one machine is NP-hard" (1990). -/
public theorem_wanted totalTardiness_npComplete :
    totalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.TotalTardiness

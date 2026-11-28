/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PRECEDENCE-CONSTRAINED
MULTIPROCESSOR SCHEDULING; J. D. Ullman, "NP-complete scheduling problems" (1975).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PrecedenceMultiprocessorSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceMultiprocessorScheduling

/-!
# PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING is NP-complete

Jobs with processing times and precedence constraints, `m` identical machines, and a deadline
`D`. The question is whether there are start times and a machine assignment meeting all
precedence constraints and the deadline, with no machine running two jobs at once (same-machine
non-overlap).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING is NP-complete.** The
precedence-constrained multiprocessor scheduling decision problem is in NP, and every decision
problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey
and D. S. Johnson, *Computers and Intractability* (1979), PRECEDENCE-CONSTRAINED
MULTIPROCESSOR SCHEDULING; J. D. Ullman, "NP-complete scheduling problems" (1975). -/
public theorem_wanted precedenceMultiprocessorScheduling_npComplete :
    precedenceMultiprocessorSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceMultiprocessorSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceMultiprocessorScheduling

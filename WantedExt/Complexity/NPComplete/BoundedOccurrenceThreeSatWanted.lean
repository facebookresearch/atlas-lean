/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-SAT WITH BOUNDED OCCURRENCES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), 3-SAT with bounded occurrences; C. A. Tovey, "A simplified NP-complete
satisfiability problem" (1984).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BoundedOccurrenceThreeSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedOccurrenceThreeSat

/-!
# 3-SAT WITH BOUNDED OCCURRENCES is NP-complete

A 3-CNF formula in which every variable occurs at most four times in total (counting positive
and negative occurrences). The question is whether the formula is satisfiable. The bound is
four: with at most three occurrences per variable, every such 3-CNF formula is satisfiable.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **3-SAT WITH BOUNDED OCCURRENCES is NP-complete.** The decision problem 3-SAT WITH BOUNDED
OCCURRENCES over bitstrings belongs to NP, and every decision problem in NP has a polynomial-time
many-one reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability: A Guide to the Theory of NP-Completeness* (1979), 3-SAT
with bounded occurrences; C. A. Tovey, "A simplified NP-complete satisfiability problem"
(1984). -/
public theorem_wanted boundedOccurrenceThreeSat_npComplete :
    boundedOccurrenceThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedOccurrenceThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.BoundedOccurrenceThreeSat

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST CYCLE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LONGEST CYCLE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LongestCycleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestCycle

/-!
# LONGEST CYCLE is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has a simple cycle with
at least `K` edges (and at least three vertices).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LONGEST CYCLE is NP-complete.** The decision problem LONGEST CYCLE belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to LONGEST CYCLE.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), LONGEST CYCLE. -/
public theorem_wanted longestCycle_npComplete :
    longestCycleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestCycleDec

end MetaMathlibExt.Complexity.NPComplete.LongestCycle

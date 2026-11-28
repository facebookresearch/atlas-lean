/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LONGEST PATH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LongestPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestPath

/-!
# LONGEST PATH is NP-complete

An undirected graph, a bound `K`, and distinguished endpoints `s` and `t` (Garey-Johnson ND29).
The question is whether the graph has a simple path from `s` to `t` with at least `K` edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LONGEST PATH is NP-complete.** The LONGEST PATH decision problem belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to LONGEST PATH.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), LONGEST PATH. -/
public theorem_wanted longestPath_npComplete :
    longestPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestPathDec

end MetaMathlibExt.Complexity.NPComplete.LongestPath

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM CUT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM CUT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCut

/-!
# MAXIMUM CUT is NP-complete

An undirected graph and a bound `K`. The question is whether the vertices can be split into two
sets with at least `K` edges crossing between them, witnessed by a sublist of at least `K`
crossing edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM CUT is NP-complete.** The decision problem MAXIMUM CUT lies in NP, and every
decision problem in NP has a polynomial-time many-one reduction to MAXIMUM CUT.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), MAXIMUM CUT. -/
public theorem_wanted maxCut_npComplete :
    maxCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCutDec

end MetaMathlibExt.Complexity.NPComplete.MaxCut

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM LINEAR ARRANGEMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM LINEAR
ARRANGEMENT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumLinearArrangementDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumLinearArrangement

/-!
# MINIMUM LINEAR ARRANGEMENT is NP-complete

An undirected graph and a bound `K`. The question is whether the vertices can be labeled with
`0, …, n - 1` (a bijection) so that the sum over edges of the label differences is at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM LINEAR ARRANGEMENT is NP-complete.** The MINIMUM LINEAR ARRANGEMENT decision problem
lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MINIMUM LINEAR ARRANGEMENT. -/
public theorem_wanted minimumLinearArrangement_npComplete :
    minimumLinearArrangementDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumLinearArrangementDec

end MetaMathlibExt.Complexity.NPComplete.MinimumLinearArrangement

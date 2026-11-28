/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NONOGRAM is NP-complete

Source:
N. Ueda and T. Nagao, "NP-completeness results for nonogram via parsimonious reductions"
(1996).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NonogramDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nonogram

/-!
# NONOGRAM is NP-complete

Row and column run-length clues for a two-color picture. The question is whether there is a
picture (rows of Booleans) whose rows and columns have exactly the given runs of consecutive
true cells, where runs are the maximal blocks of true cells in order.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NONOGRAM is NP-complete.** The NONOGRAM decision problem belongs to NP, and every decision
problem in NP reduces to NONOGRAM by a polynomial-time many-one reduction.

Source: N. Ueda and T. Nagao, "NP-completeness results for
nonogram via parsimonious reductions" (1996). -/
public theorem_wanted nonogram_npComplete :
    nonogramDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonogramDec

end MetaMathlibExt.Complexity.NPComplete.Nonogram

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET SPLITTING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SET SPLITTING (hypergraph
2-coloring); S. Lovasz, "Coverings and colorings of hypergraphs" (1973).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SetSplittingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetSplitting

/-!
# SET SPLITTING is NP-complete

A list of subsets of a universe of size `n`. The question is whether the universe can be split
into two parts so that every set meets both parts (hypergraph 2-colorability).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SET SPLITTING is NP-complete.** The SET SPLITTING decision problem belongs to NP, and every
decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), SET SPLITTING (hypergraph 2-coloring); S. Lovasz, "Coverings and
colorings of hypergraphs" (1973). -/
public theorem_wanted setSplitting_npComplete :
    setSplittingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setSplittingDec

end MetaMathlibExt.Complexity.NPComplete.SetSplitting

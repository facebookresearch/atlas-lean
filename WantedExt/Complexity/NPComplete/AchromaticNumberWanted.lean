/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACHROMATIC NUMBER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), ACHROMATIC NUMBER; M.
Farber et al., "The achromatic number of graphs" (1986).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AchromaticNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumber

/-!
# ACHROMATIC NUMBER is NP-complete

An undirected graph and a bound `K`. The question is whether the achromatic number is at least
`K`: a proper coloring using some number `q ≥ K` of colors (colors `0, …, q - 1`, all used)
such that every pair of used colors appears on some edge.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ACHROMATIC NUMBER is NP-complete.** The ACHROMATIC NUMBER decision problem belongs to NP, and
every decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), ACHROMATIC NUMBER; M. Farber et al., "The achromatic number of
graphs" (1986). -/
public theorem_wanted achromaticNumber_npComplete :
    achromaticNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L achromaticNumberDec

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumber

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSTRING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR9] SHORTEST COMMON SUPERSTRING;
J. Gallant, D. Maier and J. A. Storer, "On finding minimal length superstrings", Journal of
Computer and System Sciences 20 (1980), 50-58, doi:10.1016/0022-0000(80)90004-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShortestCommonSuperstringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring

/-!
# SHORTEST COMMON SUPERSTRING is NP-complete

INSTANCE: a finite alphabet `Σ`, a finite set `R` of strings from `Σ*`, and a positive integer
`K`. QUESTION: is there a string `w ∈ Σ*` with `|w| ≤ K` such that each string `x ∈ R` is a
substring of `w`, i.e., `w = w₀ x w₁` where each `wᵢ ∈ Σ*`?

The alphabet is `{0, …, k - 1}` for a given `k`, and strings are lists of symbols. "`x` is a
substring of `w`" is core Lean's `List.IsInfix` (`x <:+: w`), defined as
`∃ s t, s ++ x ++ t = w`, the source's `w = w₀ x w₁`. The set `R` is given as a list; a repeated
entry repeats a constraint and changes nothing.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHORTEST COMMON SUPERSTRING is NP-complete.** Source: Garey and Johnson (1979), [SR9];
Gallant, Maier and Storer (1980). -/
public theorem_wanted shortestCommonSuperstring_npComplete :
    shortestCommonSuperstringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestCommonSuperstringDec

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring

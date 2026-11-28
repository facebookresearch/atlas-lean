/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAGNETS is NP-complete

Source:
J. Kölker, "The Magnets puzzle is NP-complete", Journal of Information Processing 20(3)
(2012), 707-708, doi:10.2197/ipsjjip.20.707 (Section 1, Theorem 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MagnetsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Magnets

/-!
# MAGNETS is NP-complete

Kölker's Magnets puzzle. INSTANCE: a `w × h` rectangle, a subdivision of this rectangle into
dominoes, and `2(w + h)` integers `rᵢ⁺, rᵢ⁻, cⱼ⁺, cⱼ⁻` for `i = 0, …, h - 1` and
`j = 0, …, w - 1`. QUESTION: can a value in `{-1, 0, +1}` be assigned to each square such that
(1) the two values in each domino sum to `0`; (2) every pair `(x, y)` of horizontally or
vertically adjacent values satisfies `x = y = 0 ∨ x ≠ y`; and (3) in each row `i`, `+1`
occurs `rᵢ⁺` times and `-1` occurs `rᵢ⁻` times, and in each column `j`, `+1` occurs `cⱼ⁺`
times and `-1` occurs `cⱼ⁻` times?

Squares are pairs `(i, j)` of a row `i < h` and a column `j < w`; adjacency is the grid
graph `pathGraph h □ pathGraph w`. Values are Mathlib's `SignType` (`-1`, `0`, `1`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAGNETS is NP-complete.** Source: Kölker (2012), Theorem 1 (membership: a solution is
a certificate; hardness: a reduction from monotone 1-in-3 satisfiability). -/
public theorem_wanted magnets_npComplete :
    magnetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L magnetsDec

end MetaMathlibExt.Complexity.NPComplete.Magnets

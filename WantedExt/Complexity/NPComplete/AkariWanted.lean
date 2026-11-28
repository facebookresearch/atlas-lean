/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AKARI (LIGHT UP) is NP-complete

Source:
Brandon McPhail, "Light Up is NP-complete", unpublished manuscript, 2005.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AkariDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Akari

/-!
# AKARI (LIGHT UP) is NP-complete

A board of cells: `0` empty, `1` wall, `2 + k` a numbered wall requiring exactly `k`
orthogonally adjacent bulbs. The question is whether bulbs can be placed on empty cells so that
every empty cell is illuminated (a bulb shines along its row and column until a wall), no bulb
illuminates another bulb, and every numbered wall has exactly the indicated number of
orthogonally adjacent bulbs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **AKARI (LIGHT UP) is NP-complete.** The Akari decision problem belongs to NP, and every
decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: Brandon McPhail, "Light Up is NP-complete",
unpublished manuscript, 2005. -/
public theorem_wanted akari_npComplete :
    akariDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L akariDec

end MetaMathlibExt.Complexity.NPComplete.Akari

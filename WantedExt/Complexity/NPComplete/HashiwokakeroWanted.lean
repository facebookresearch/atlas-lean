/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HASHIWOKAKERO is NP-complete

Source:
D. Andersson, "Hashiwokakero is NP-complete", Information Processing Letters 109(19) (2009),
1145-1146, doi:10.1016/j.ipl.2009.07.017.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HashiwokakeroDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Hashiwokakero

/-!
# HASHIWOKAKERO (BRIDGES) is NP-complete

INSTANCE: a finite set of islands at integer grid points, each labelled with an integer in
`{1, …, 8}`.
QUESTION: can horizontal and vertical bridges be drawn between islands, at most two between a
pair, with no crossings, so that each island has exactly its label's number of bridges and the
bridges connect the islands into a single connected group?

The islands are listed as `(x, y, ℓ)`: position `(x, y)` and label `ℓ`. Positions are natural
numbers; any finite set of integer grid points can be translated into this quadrant, which
changes nothing in the puzzle. A solution gives every pair of islands `a, b` a number of bridges
`bridges a b = bridges b a ≤ 2`. A bridge runs straight between two distinct islands in the same
row or the same column, and may not pass over another island (`Visible`): no island lies
strictly between its ends on its line. A horizontal and a vertical bridge cross when each passes
strictly between the ends of the other (`Cross`); two bridges on one line cannot overlap without
passing over an island, so this is the only way bridges cross. The islands are connected when
the graph joining islands with at least one bridge between them is preconnected (any two islands
are joined by a chain of bridges); the island set is nonempty (`WellFormed`), so this is a
single connected group.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HASHIWOKAKERO is NP-complete.** Source: Andersson (2009). -/
public theorem_wanted hashiwokakero_npComplete :
    hashiwokakeroDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hashiwokakeroDec

end MetaMathlibExt.Complexity.NPComplete.Hashiwokakero

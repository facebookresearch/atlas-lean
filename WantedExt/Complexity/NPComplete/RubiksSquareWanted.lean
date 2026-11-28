/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RUBIK'S SQUARE is NP-complete

Source:
E. D. Demaine, S. Eisenstat and M. Rudoy, "Solving the Rubik's Cube Optimally is NP-complete",
35th Symposium on Theoretical Aspects of Computer Science (STACS 2018), LIPIcs 96 (2018),
24:1-24:13, doi:10.4230/LIPIcs.STACS.2018.24, Problem 1 (the Rubik's Square problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RubiksSquareDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RubiksSquare

/-!
# RUBIK'S SQUARE is NP-complete

The `n × n` Rubik's Square (the `n × n × 1` Rubik's Cube) is an `n × n` array of unit cubies;
every cubie face on the outside of the puzzle carries a sticker of one of six colours. A move
flips a single row or column of cubies through space by a rotation in the long direction
(Demaine, Eisenstat and Rudoy, Section 2.1): the half turn about the axis that lies in the plane
of the square and is perpendicular to the row or column, so that the cubie at `(x, y)` of a
flipped row moves to `(-x, y)` in coordinates centred at the origin (Section 2.3), turned upside
down. The puzzle is solved when each of its six faces is monochromatic in a different colour. Given a configuration and a number `k`, the question is
whether the configuration can be solved in `k` moves or fewer.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RUBIK'S SQUARE is NP-complete.** Source: Demaine, Eisenstat and Rudoy (2018), Problem 1. -/
public theorem_wanted rubiksSquare_npComplete :
    rubiksSquareDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rubiksSquareDec

end MetaMathlibExt.Complexity.NPComplete.RubiksSquare

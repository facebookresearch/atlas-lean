/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TETRAVEX is NP-complete

Source:
Y. Takenaga and T. Walsh, "Tetravex is NP-complete", Information Processing Letters 99 (2006),
171-174, doi:10.1016/j.ipl.2006.04.010 (arXiv:0903.1147).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TetravexDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Tetravex

/-!
# TETRAVEX is NP-complete

INSTANCE: a side length `n` and `n²` unit square tiles, each edge of which is labelled with a
number. QUESTION: can each tile be placed within an
`n × n` square, every tile used exactly once and none rotated, such that all neighbouring
edges are labelled with an identical number?

A tile `(a, b, c, d)` has top label `a`, right label `b`, bottom label `c` and left label `d`.
Positions `(x, y)` with `x, y < n` count columns left to right and rows top to bottom. The
tiles form a list, so equal tiles may occur several times; each list entry is placed once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TETRAVEX is NP-complete.** Source: Takenaga and Walsh (2006). -/
public theorem_wanted tetravex_npComplete :
    tetravexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tetravexDec

end MetaMathlibExt.Complexity.NPComplete.Tetravex

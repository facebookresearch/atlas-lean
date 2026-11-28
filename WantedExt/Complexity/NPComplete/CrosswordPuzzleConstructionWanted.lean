/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CROSSWORD PUZZLE CONSTRUCTION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GP14] CROSSWORD PUZZLE
CONSTRUCTION (credited there to Lewis and Papadimitriou);
J. Engel, M. Holzer, O. Ruepp, and F. Sehnke, "On computer integrated rationalized
crossword puzzle manufacturing", Fun with Algorithms (FUN 2012), Lecture Notes in
Computer Science 7288 (2012), 131-141, doi:10.1007/978-3-642-30347-0_15 (records the
attribution).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CrosswordPuzzleConstructionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstruction

/-!
# CROSSWORD PUZZLE CONSTRUCTION is NP-complete

INSTANCE: a finite set `W ⊆ Σ*` of words and an `n × n` matrix `A` of `0`'s and `1`'s.
QUESTION: can an `n × n` crossword puzzle be built from the words in `W` and blank squares
corresponding to the `1`'s of `A`, that is, if `E` is the set of pairs `(i, j)` with
`A i j = 0`, is there an assignment `f : E → Σ` such that the letters assigned to any maximal
horizontal or vertical contiguous sequence of members of `E` form, in order, a word of `W`?

Letters are natural numbers. A run that is maximal is bounded on each side by a `1` of `A`
(a blank square) or by the border of the square. Following the source literally, a maximal
run of a single square is also a run, so it must spell a one-letter word of `W`. Words may be
used any number of times. Vertical runs are read top to bottom and horizontal runs left to
right.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CROSSWORD PUZZLE CONSTRUCTION is NP-complete.** Source: Garey and Johnson (1979),
[GP14]; Engel, Holzer, Ruepp, and Sehnke (2012). -/
public theorem_wanted crosswordPuzzleConstruction_npComplete :
    crosswordPuzzleConstructionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L crosswordPuzzleConstructionDec

end MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstruction

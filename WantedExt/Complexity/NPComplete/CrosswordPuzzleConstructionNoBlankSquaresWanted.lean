/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CROSSWORD PUZZLE CONSTRUCTION with no blank squares is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GP14] CROSSWORD PUZZLE CONSTRUCTION, p. 258,
comment: "Remains NP-complete even if all entries in A are 0" (the entry's reference is
[Lewis and Papadimitriou, 1978]: H. R. Lewis and C. H. Papadimitriou, "The efficiency of
algorithms", Scientific American 238(1) (1978), 96-109, doi:10.1038/scientificamerican0178-96).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CrosswordPuzzleConstructionNoBlankSquaresDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstructionNoBlankSquares

open MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstruction
  (CrosswordPuzzleConstructionInstance CrosswordPuzzleConstructionFeasible)

/-!
# CROSSWORD PUZZLE CONSTRUCTION with no blank squares is NP-complete

INSTANCE: a finite set `W ⊆ Σ*` of words and an `n × n` matrix `A` of `0`'s and `1`'s in which
every entry is `0`.
QUESTION: can an `n × n` crossword puzzle be built from the words in `W` and blank squares
corresponding to the `1`'s of `A` (here: no blank squares), i.e., if `E` is the set of pairs
`(i, j)` with `A i j = 0`, is there an assignment `f : E → Σ` such that the letters assigned to
any maximal horizontal or vertical contiguous sequence of members of `E` form, in order, a word
of `W`?

With every entry `0`, `E` is the whole square, so the maximal runs are the `n` rows and the `n`
columns: the question asks for an `n × n` array of letters whose rows (left to right) and
columns (top to bottom) are words of `W`.

The instance, the matrix encoding, `WellFormed` and the question are those of
`CrosswordPuzzleConstruction` ([GP14]); this module adds the restriction that every entry of
`A` is `0` (`false`) to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CROSSWORD PUZZLE CONSTRUCTION with no blank squares is NP-complete.** Source: Garey and
Johnson (1979), [GP14], comment; Lewis and Papadimitriou (1978). -/
public theorem_wanted crosswordPuzzleConstructionNoBlankSquares_npComplete :
    crosswordPuzzleConstructionNoBlankSquaresDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L crosswordPuzzleConstructionNoBlankSquaresDec

end MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstructionNoBlankSquares

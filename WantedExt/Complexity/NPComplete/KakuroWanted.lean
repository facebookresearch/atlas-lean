/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KAKURO (CROSS SUM) is NP-complete

Source:
T. Seta, "The complexities of puzzles, cross sum and their another solution problems (ASP)",
senior thesis, Department of Information Science, University of Tokyo (2002), Section 2.1;
T. Yato and T. Seta, "Complexity and completeness of finding another solution and its
application to puzzles", IEICE Transactions on Fundamentals of Electronics, Communications and
Computer Sciences E86-A(5) (2003), 1052-1060.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KakuroDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kakuro

/-!
# KAKURO (CROSS SUM) is NP-complete

Seta (2002), Section 2.1.1, defines the puzzle (Nikoli's Kakuro):

Input: a `W × H` board such that
1. "The board is made of white boxes and black boxes."
2. "Numbers called sum are given one for each vertical or horizontal line of white boxes. (And
   the numbers are put in the black boxes on the beginning of the white line.)"
3. "White boxes are connected, not separated by black boxes."
4. "Black boxes can be located next to each other not like CROSS WORD."
5. "Any line of white boxes has at least two white boxes."

Question: is there a setting of numbers in the white boxes such that
6. "Numbers in white boxes are from 1 to 9."
7. "The sum of numbers in one line is same to the given sum."
8. "Any number appears at most once in one white line."

Seta proves this NP-complete (Section 2.1); Yato and Seta (2003) prove its another-solution
problem ASP-complete, which implies NP-completeness.

Representation. The board is given row by row; a cell is a triple `(w, h, v)` with `w = true`
for a white box. A line is a maximal horizontal or vertical run of white boxes. Instead of
writing a line's sum in the black box before it, the sum is stored in the line's first white
box: `h` is the sum of the horizontal line that starts at this box and `v` that of the vertical
line, and both are `0` wherever no line starts (`WellFormed`). Thus each line carries exactly
one sum, and the representation also covers lines that start at the edge of the board. A box
starts a horizontal line when it is white and the box to its left is black or off the board
(`HStart`); the line consists of the white boxes from it to the right up to the next black box
or the edge (`hLen` boxes). Vertical lines are read downward in the same way. Clause 3 is
`SimpleGraph.Connected` (nonempty and preconnected) of the subgraph that Mathlib's grid graph
`pathGraph H □ pathGraph W` induces on the white boxes; clause 4 needs no condition; clause 5
says `2 ≤ hLen` and `2 ≤ vLen` at every line start. A setting is a function `ℕ → ℕ → ℕ` read
on the white boxes. The instance size is proportional to the area of the board plus the binary
length of the sums.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **KAKURO (CROSS SUM) is NP-complete.** Source: Seta (2002), Section 2.1; Yato and Seta
(2003). -/
public theorem_wanted kakuro_npComplete :
    kakuroDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kakuroDec

end MetaMathlibExt.Complexity.NPComplete.Kakuro

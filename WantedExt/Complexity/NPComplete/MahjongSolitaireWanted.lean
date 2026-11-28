/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAHJONG SOLITAIRE with perfect information is NP-complete

Source:
M. de Bondt, "Solving Mahjong Solitaire boards with peeking", arXiv:1203.6559 (2012),
Theorems 2 and 3, https://arxiv.org/abs/1203.6559 (Theorem 2 is credited there to
D. Eppstein, "Computational complexity of games and puzzles", entry Shanghai,
https://ics.uci.edu/~eppstein/cgt/hard.html);
model of the game: A. Condon, J. Feigenbaum, C. Lund and P. Shor, "Random debaters and the
hardness of approximating stochastic functions", SIAM Journal on Computing 26(2) (1997),
369-400, Section 3.4, doi:10.1137/S0097539793260738.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MahjongSolitaireDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MahjongSolitaire

/-!
# MAHJONG SOLITAIRE with perfect information is NP-complete

Mahjong Solitaire (Shanghai) is played with Mahjong tiles, divided into sets of two or four
matching tiles, organized in rows that may be stacked on top of each other. A tile that is not
hidden under another tile and is at the end of its row is available; in a move, a pair of
available matching tiles is removed. With perfect information ("peeking") the player knows every
tile, hidden ones included.

INSTANCE: an arrangement of tiles in stacked rows, with the face of every tile known.
QUESTION: can all tiles be removed by a sequence of moves?

The arrangement follows Condon, Feigenbaum, Lund and Shor (Section 3.4). A configuration is a
set of positions `(i, j, k)` of natural numbers (row `i`, place `j` in the row, height `k`) with
no gaps in a row (with `(i, j, k)` and `(i, j', k)`, every `(i, j'', k)` with
`j ≤ j'' ≤ j'` is present) and a tile under every tile above height `0` (with `(i, j, k)` and
`k > 0`, `(i, j, k - 1)` is present). A position `(i, j, k)` is hidden when `(i, j, k + 1)` is
present, and available when it is not hidden and `(i, j - 1, k)` or `(i, j + 1, k)` is absent
(for `j = 0` there is no position `(i, j - 1, k)`). Each set of matching tiles has two or four
tiles. A move removes two available tiles of the same set; a sequence of moves wins when no tile
is left.

The instance lists the tiles as `(i, j, k, s)`: position `(i, j, k)` and the index `s` of its set
of matching tiles. `WellFormed` requires distinct positions forming a configuration, and two or
four tiles in each set. De Bondt proves NP-hardness already for arrangements of isolated stacks
of three tiles (rows of length one), with four tiles in each set (Theorem 3); membership in NP
holds because a winning sequence is a certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAHJONG SOLITAIRE with perfect information is NP-complete.** Source: de Bondt (2012),
Theorems 2 and 3; model of Condon, Feigenbaum, Lund and Shor (1997). -/
public theorem_wanted mahjongSolitaire_npComplete :
    mahjongSolitaireDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mahjongSolitaireDec

end MetaMathlibExt.Complexity.NPComplete.MahjongSolitaire

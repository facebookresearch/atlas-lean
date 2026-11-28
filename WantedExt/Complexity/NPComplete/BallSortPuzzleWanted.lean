/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BALL SORT PUZZLE is NP-complete

Source:
T. Ito, J. Kawahara, S. Minato, Y. Otachi, T. Saitoh, A. Suzuki, R. Uehara, T. Uno,
K. Yamanaka and R. Yoshinaka, "Sorting balls and water: equivalence and computational
complexity", Theoretical Computer Science 978 (2023), 114158, doi:10.1016/j.tcs.2023.114158,
Theorem 9 (BSP); arXiv:2202.09495.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BallSortPuzzleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BallSortPuzzle

/-!
# BALL SORT PUZZLE is NP-complete

Ito et al. (2023), Section 1: "We are given `n + k` bins of capacity `h`. In an initial
configuration, `n` bins are full (i.e., filled with `h` units) and `k` bins are empty, where
each unit has a color in the color set `C`. Our task is to fill `n` bins monochromatically ...
We define BSP ... as the problem of deciding whether a given initial configuration can be
reconfigured to a sorted configuration by a sequence of ball moves." Section 2.1: a
configuration is a map `S : B → C^{≤h}` (each bin a sequence of at most `h` colors, bottom to
top); a bin is sorted under `S` if `S(b) ∈ {ε, c^h}` for some `c ∈ C`, and `S` is sorted if all
bins are; "A ball-move can modify a configuration `S` into `S'` ... if there are `b₁, b₂ ∈ B`
and `c ∈ C` such that `S(b₁) = S'(b₁) · c`, `TC(S(b₂)) ∈ {c, ε}`, `S'(b₂) = S(b₂) · c`, and
`S(b) = S'(b)` for all `b ∈ B \ {b₁, b₂}`", where `TC` is the top color (`ε` for an empty bin).
Theorem 9: BSP is NP-complete (even with two colors). The paper encodes the `k` empty bins by
the number `k` ("`Θ(nh log |C| + log k)` bits").

INSTANCE: a capacity `h`, a number `k` of empty bins, and `n` full bins, each a sequence of `h`
colors.
QUESTION: can ball moves turn the configuration (the `n` full bins and `k` empty bins) into one
in which every bin is empty or holds `h` balls of one color?

Representation. Colors are natural numbers; a bin is the list of its colors from bottom to top;
a configuration is the list of its bins (the full bins, then `k` empty ones). A ball move takes
the top ball `c` of bin `b₁` and puts it on bin `b₂ ≠ b₁` when `b₂` is empty or has top `c`, and
holds fewer than `h` balls (so that `S'(b₂)` has length at most `h`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BALL SORT PUZZLE is NP-complete.** Source: Ito et al. (2023), Theorem 9. -/
public theorem_wanted ballSortPuzzle_npComplete :
    ballSortPuzzleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ballSortPuzzleDec

end MetaMathlibExt.Complexity.NPComplete.BallSortPuzzle

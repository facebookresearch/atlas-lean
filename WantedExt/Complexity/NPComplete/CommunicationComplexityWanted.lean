/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMUNICATION COMPLEXITY is NP-complete

Source:
S. Hirahara, R. Ilango and B. Loff, "Communication complexity is NP-hard", arXiv:2507.10426
(2025);
S. Gaspers, T. Z. He and S. Mackenzie, "NP-hardness and additive inapproximability of
deterministic communication complexity", arXiv:2508.05597 (2025);
A. C.-C. Yao, "Some complexity questions related to distributive computing", Proceedings of the
11th Annual ACM Symposium on Theory of Computing (1979), 209-213, doi:10.1145/800135.804414;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 5 (1984),
595-609, doi:10.1016/0196-6774(84)90010-5, entry [1] COMMUNICATION COMPLEXITY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CommunicationComplexityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommunicationComplexity

/-!
# COMMUNICATION COMPLEXITY is NP-complete

INSTANCE: finite sets `X` and `Y`, a function `f : X × Y → {0, 1}` given by its table (the
communication matrix), and a positive integer `K`.
QUESTION: is the deterministic two-party communication complexity of `f` at most `K`, i.e., is
there a protocol by which a player holding `x ∈ X` and a player holding `y ∈ Y` determine
`f(x, y)` for every input pair while exchanging at most `K` bits?

Yao (1979) defined the measure and asked whether computing it is NP-complete. Hirahara, Ilango
and Loff (2025) state that deciding `CC(f) ≤ k` from the communication matrix and `k` is easily
seen to be in NP, and prove it NP-hard; Gaspers, He and Mackenzie (2025) prove NP-hardness
independently, both in the standard model used here and in Yao's original convention.
Johnson's column (1984) lists the problem as COMMUNICATION COMPLEXITY (instance: two finite sets
`X` and `Y` of strings of length `n`, a function `f : X × Y → {0, 1}`, a positive integer `K`),
in Yao's original convention, where the players alternate bits and the receiver of the last bit
determines the answer, citing Papadimitriou and Tsitsiklis (1982).

The measure is the standard one: a protocol is a binary tree whose inner nodes are owned by one
player and labelled by a function of that player's input (the bit sent), and whose leaves are
labelled by an output; on input `(x, y)` the protocol follows the sent bits from the root to a
leaf, and its cost is the depth of the tree, the number of bits exchanged on the worst input.
`CC(f) ≤ K` means that some protocol of depth at most `K` outputs `f(x, y)` on every input. Since
the first player can send the index of `x` and the second player the answer, `CC(f)` is at most
`⌈log₂ |X|⌉ + 1`, so a witnessing tree has polynomially many nodes.

The rows of the matrix are the elements of `X`, indexed `0, …, m - 1`, and its columns the
elements of `Y`, indexed `0, …, n - 1`; the strings that name them in Johnson's statement play no
role. The matrix is a list of `m` rows, each a list of `n` Booleans (`WellFormed`), and
`WellFormed` requires `0 < K` (the column's positive integer `K`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COMMUNICATION COMPLEXITY is NP-complete.** Source: Hirahara, Ilango and Loff (2025);
Gaspers, He and Mackenzie (2025); Yao (1979); Johnson (1984), NP-completeness column. -/
public theorem_wanted communicationComplexity_npComplete :
    communicationComplexityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L communicationComplexityDec

end MetaMathlibExt.Complexity.NPComplete.CommunicationComplexity

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATRIX COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 282, problem [MS13] MATRIX
COVER (credited there to Garey and Johnson, unpublished; transformation from
MAX CUT), with the comparison reversed: the entry prints `≥ K`, and this module
states `≤ K`, the question that the cited MAX CUT transformation proves
NP-hard (see the module docstring). The `≤ K` reading, with the target
`K' = 2(|E| - 2K)` for a MAX CUT bound `K`, is the one in S. McCulloch,
"Discussions of NP-Complete Problems", entry for MS13 Matrix Cover,
https://npcomplete.owu.edu/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MatrixCoverDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatrixCover

/-!
# MATRIX COVER is NP-complete

INSTANCE: an `n × n` matrix `A = (a i j)` with nonnegative integer entries, and an integer
`K`. QUESTION: is there a function `f : {1, ..., n} → {-1, +1}` such that
`∑_{1 ≤ i, j ≤ n} a i j * f i * f j ≤ K`?

The comparison is `≤`. Garey and Johnson's entry (p. 282) prints `≥ K`; read literally, that
question is decidable in polynomial time, and it is not the question that the cited MAX CUT
transformation proves NP-hard. With nonnegative entries every term satisfies
`a i j * f i * f j ≤ a i j`, so the constant function `f = +1` maximizes the sum and the
question with `≥` is decidable by adding up the entries. The `≤` question is the one the
transformation from MAX CUT proves NP-hard: for the adjacency matrix of a graph, the sum is
`2 * (|E| - 2 * c)` where `c` is the number of edges `f` cuts.

Indices are `0, ..., n - 1` here. Entries are natural numbers in binary; `K` is the integer
`K.1 - K.2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MATRIX COVER (with `≤ K`) is NP-complete.** Source: Garey and Johnson (1979), p. 282,
[MS13], which prints `≥ K`; the `≤ K` question is the one its cited MAX CUT transformation
proves NP-hard, as in McCulloch's discussion of MS13. -/
public theorem_wanted matrixCover_npComplete :
    matrixCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L matrixCoverDec

end MetaMathlibExt.Complexity.NPComplete.MatrixCover

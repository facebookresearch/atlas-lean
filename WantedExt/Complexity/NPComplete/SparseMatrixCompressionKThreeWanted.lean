/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SPARSE MATRIX COMPRESSION with K = 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), p. 229, problem [SR13] SPARSE MATRIX COMPRESSION
(comment: remains NP-complete for fixed `K = 3`; reference: [Even, Lichtenstein, and
Shiloach, 1977]);
S. Even, D. I. Lichtenstein and Y. Shiloach, "Remarks on Ziegler's method for matrix
compression", unpublished manuscript (1977);
V. Jugé, D. Köppl, V. Limouzy, A. Marino, J. Olblich, G. Punzi and T. Uno, "Revisiting the
sparse matrix compression problem", arXiv:2602.15314 (2026), Section 1 (records that the
problem is NP-complete even if the maximum needed shift is at most two).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SparseMatrixCompressionKThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompressionKThree

open MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompression

/-!
# SPARSE MATRIX COMPRESSION with K = 3 is NP-complete

INSTANCE: an `m × n` matrix `A` with entries `a_ij ∈ {0, 1}`, `1 ≤ i ≤ m`, `1 ≤ j ≤ n`, and
the integer `K = 3`, where `K ≤ mn`.
QUESTION: is there a sequence `(b₁, b₂, ..., b_{n+K})` of integers `bᵢ`, each satisfying
`0 ≤ bᵢ ≤ m`, and a function `s : {1, 2, ..., m} → {1, 2, ..., K}` such that, for `1 ≤ i ≤ m`
and `1 ≤ j ≤ n`, the entry `a_ij = 1` if and only if `b_{s(i)+j-1} = i`?

This is the restriction of `WantedExt.Complexity.NPComplete.SparseMatrixCompressionWanted`
([SR13]) to instances with `K = 3`. The instance type, the parent well-formedness condition and
the question are that module's (`SparseMatrixCompressionInstance`,
`SparseMatrixCompression.WellFormed`, `SparseMatrixCompressionFeasible`): the instance is
`(n, rows of A, K)` with every row of length `n` and `0 < K ≤ mn`, and rows, columns, shifts and
positions of `b` are indexed from `0` as described there. `WellFormed` adds the restriction
`K = 3`; together with the parent bound `K ≤ mn` this keeps exactly the [SR13] instances whose
bound is `3`. With `K = 3` the shifts `s(i) - 1` lie in `{0, 1, 2}`, which is the "maximum shift
at most two" of Jugé et al. (2026).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SPARSE MATRIX COMPRESSION with `K = 3` is NP-complete.** Source: Garey and Johnson
(1979), [SR13]; Even, Lichtenstein and Shiloach (1977). -/
public theorem_wanted sparseMatrixCompressionKThree_npComplete :
    sparseMatrixCompressionKThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sparseMatrixCompressionKThreeDec

end MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompressionKThree

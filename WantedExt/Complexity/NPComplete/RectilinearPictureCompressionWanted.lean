/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR PICTURE COMPRESSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR25] RECTILINEAR PICTURE
COMPRESSION, p. 232 (reference [Masek, 1978]: W. J. Masek, "Some NP-complete set covering
problems", unpublished manuscript, as listed in Garey and Johnson's references; transformation
from 3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RectilinearPictureCompressionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearPictureCompression

/-!
# RECTILINEAR PICTURE COMPRESSION is NP-complete

INSTANCE: an `n × n` matrix `M` of `0`'s and `1`'s, and a positive integer `K`.
QUESTION: is there a collection of `K` or fewer rectangles that covers precisely those entries
in `M` that are `1`'s, i.e., is there a sequence of quadruples `(aᵢ, bᵢ, cᵢ, dᵢ)`, `1 ≤ i ≤ K`,
where `aᵢ ≤ bᵢ`, `cᵢ ≤ dᵢ`, such that for every pair `(i, j)`, `1 ≤ i, j ≤ n`, `M_{ij} = 1` if
and only if there exists a `k`, `1 ≤ k ≤ K`, such that `a_k ≤ i ≤ b_k` and `c_k ≤ j ≤ d_k`?

The matrix is a list of `n` rows, each a list of `n` booleans (`true` for `1`). Rows, columns and
rectangle bounds are indexed from `0` rather than `1`, a shift that maps rectangles to rectangles.
The rectangles are a list of at most `K` quadruples (a sequence of exactly `K` quadruples may
repeat one, so "`K` or fewer" and "exactly `K`" agree when `K > 0`, and a sequence with no
rectangles covers no entry); a quadruple may extend beyond the matrix, as in the source, where
only the entries `1 ≤ i, j ≤ n` are constrained. Strong NP-completeness is immaterial here: the
matrix is given entry by entry.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECTILINEAR PICTURE COMPRESSION is NP-complete.** Source: Garey and Johnson (1979),
[SR25] (Masek, 1978). -/
public theorem_wanted rectilinearPictureCompression_npComplete :
    rectilinearPictureCompressionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectilinearPictureCompressionDec

end MetaMathlibExt.Complexity.NPComplete.RectilinearPictureCompression

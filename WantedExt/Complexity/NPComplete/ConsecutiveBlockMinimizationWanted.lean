/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSECUTIVE BLOCK MINIMIZATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR17] CONSECUTIVE
BLOCK MINIMIZATION;
L. T. Kou, "Polynomial complete consecutive information retrieval problems",
SIAM Journal on Computing 6 (1977), 67-75, doi:10.1137/0206004.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConsecutiveBlockMinimizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsecutiveBlockMinimization

/-!
# CONSECUTIVE BLOCK MINIMIZATION is NP-complete

INSTANCE: an `m × n` matrix `A` of `0`'s and `1`'s and a positive integer `K`. QUESTION: is
there a permutation of the columns of `A` that yields a matrix `B` with at most `K` blocks of
consecutive `1`'s, that is, at most `K` entries `b_ij` with `b_ij = 1` and either `j = n` or
`b_{i, j+1} = 0`?

The matrix is a list of `m` rows, each a list of `n` Booleans (`true` for `1`). Rows and columns
are indexed from `0`, so column `n - 1` is the last one. A permutation of the columns is
`σ : Equiv.Perm (Fin n)`: column `j` of `B` is column `σ j` of `A`. The entry `b_ij` is
`permutedEntry`, extended by `false` beyond the last column, so "`j` is the last column or
`b_{i, j+1} = 0`" is `permutedEntry i σ r (j + 1) = false`; each such entry ends one maximal block
of consecutive `1`'s in its row.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONSECUTIVE BLOCK MINIMIZATION is NP-complete.** Source: Garey and Johnson (1979),
[SR17]; Kou (1977). -/
public theorem_wanted consecutiveBlockMinimization_npComplete :
    consecutiveBlockMinimizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L consecutiveBlockMinimizationDec

end MetaMathlibExt.Complexity.NPComplete.ConsecutiveBlockMinimization

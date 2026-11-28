/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCULAR BLOCK MINIMIZATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR17] CONSECUTIVE BLOCK
MINIMIZATION, p. 230, comment: "Remains NP-complete if "j = n" is replaced by "j = n and
b_i1 = 0" [Booth, 1975]";
K. S. Booth, *PQ-tree algorithms*, Ph.D. thesis, University of California, Berkeley (1975), as
cited by Garey and Johnson (the thesis itself was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CircularBlockMinimizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularBlockMinimization

open ConsecutiveBlockMinimization

/-!
# CIRCULAR BLOCK MINIMIZATION is NP-complete

INSTANCE: an `m × n` matrix `A` of `0`'s and `1`'s and a positive integer `K`. QUESTION: is
there a permutation of the columns of `A` that yields a matrix `B` with at most `K` entries
`b_ij` such that `b_ij = 1` and either `j < n` and `b_{i, j+1} = 0`, or `j = n` and `b_i1 = 0`?

This is the variant of CONSECUTIVE BLOCK MINIMIZATION
(`WantedExt.Complexity.NPComplete.ConsecutiveBlockMinimizationWanted`) in Garey and Johnson's
comment to [SR17], in which "`j = n`" is replaced by "`j = n` and `b_i1 = 0`": blocks of
consecutive `1`'s are counted circularly: a block that runs from the last column on into the
first columns of its row is counted once, at its last `1`. As in that wording, a row of `B`
consisting only of `1`'s has no such entry.

The instance type, the well-formedness condition and the entries `b_ij` of the permuted matrix
are those of the parent module (`ConsecutiveBlockMinimizationInstance`, `WellFormed`,
`permutedEntry`, which extends `B` by `0` beyond the last column). Rows and columns are indexed
from `0`, so the last column is `n - 1` and the first is `0`: an entry `b_rj = 1` is counted when
`b_{r, j+1} = 0` and, if `j` is the last column, also `b_{r, 0} = 0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CIRCULAR BLOCK MINIMIZATION is NP-complete.** Source: Garey and Johnson (1979), [SR17],
comment; Booth (1975). -/
public theorem_wanted circularBlockMinimization_npComplete :
    circularBlockMinimizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circularBlockMinimizationDec

end MetaMathlibExt.Complexity.NPComplete.CircularBlockMinimization

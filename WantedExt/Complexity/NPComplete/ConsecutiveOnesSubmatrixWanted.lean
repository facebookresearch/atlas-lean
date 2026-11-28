/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSECUTIVE ONES SUBMATRIX is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR14] CONSECUTIVE ONES SUBMATRIX (reference:
[Booth, 1975]; transformation from HAMILTONIAN PATH);
M. T. Hajiaghayi and Y. Ganjali, "A note on the Consecutive Ones Submatrix problem", Information
Processing Letters 83 (2002), 163-166, doi:10.1016/S0020-0190(01)00325-8;
J. Tan and L. Zhang, "The Consecutive Ones Submatrix problem for sparse matrices", Algorithmica
48 (2007), 287-299, doi:10.1007/s00453-007-0118-z.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConsecutiveOnesSubmatrixDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesSubmatrix

open MetaMathlibExt.Complexity.NPComplete.ConsecutiveBlockMinimization
  (ConsecutiveBlockMinimizationInstance)

/-!
# CONSECUTIVE ONES SUBMATRIX is NP-complete

INSTANCE: an `m × n` matrix `A` of `0`'s and `1`'s and a positive integer `K`.
QUESTION: is there an `m × K` submatrix `B` of `A` that has the "consecutive ones" property,
i.e., such that the columns of `B` can be permuted so that in each row all the `1`'s occur
consecutively?

The instance format and its well-formedness are those of CONSECUTIVE BLOCK MINIMIZATION
(`ConsecutiveBlockMinimizationWanted`): the number `n` of columns, the `m` rows (each a list of
`n` entries, `true` for `1`), and `K`, with every row of length `n` and `K` positive. Choosing
the `K` columns of `B` and then a permutation of them is the same as choosing an injective map
`f : Fin K → Fin n`: column `j` of the permuted `B` is column `f j` of `A`. The `1`'s of a row
occur consecutively when every column between two columns holding a `1` also holds a `1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONSECUTIVE ONES SUBMATRIX is NP-complete.** Source: Garey and Johnson (1979), [SR14];
Hajiaghayi and Ganjali (2002). -/
public theorem_wanted consecutiveOnesSubmatrix_npComplete :
    consecutiveOnesSubmatrixDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L consecutiveOnesSubmatrixDec

end MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesSubmatrix

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSECUTIVE ONES MATRIX AUGMENTATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR16] CONSECUTIVE ONES MATRIX
AUGMENTATION, p. 229 (references: [Booth, 1975], [Papadimitriou, 1976a]; transformation from
OPTIMAL LINEAR ARRANGEMENT);
K. S. Booth, *PQ-Tree Algorithms*, Ph.D. thesis, University of California, Berkeley (1975);
W. Lipski, Jr., "Generalizations of the consecutive ones property and related NP-complete
problems", Coordinated Science Laboratory Report T-67, University of Illinois at
Urbana-Champaign (1978), hdl:2142/74046 (records the result as Booth's, Problem 3).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentation

/-!
# CONSECUTIVE ONES MATRIX AUGMENTATION is NP-complete

INSTANCE: an `m × n` matrix `A` of `0`'s and `1`'s and a positive integer `K`. QUESTION: is
there a matrix `A'`, obtained from `A` by changing `K` or fewer `0` entries to `1`'s, such that
`A'` has the consecutive ones property, i.e. the columns of `A'` can be permuted so that in
each row all the `1`'s occur consecutively?

The matrix is a list of `m` rows, each a list of `n` Booleans (`true` for `1`); rows and columns
are indexed from `0`. The matrix `A'` is a function `B : Fin m → Fin n → Bool` that is `1`
wherever `A` is `1`; the changed entries are the positions where `A` is `0` and `B` is `1`. A
permutation of the columns is `σ : Equiv.Perm (Fin n)`: column `j` of the permuted matrix is
column `σ j` of `B`. The `1`'s of a row occur consecutively when every position between two
`1`'s of the row holds a `1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONSECUTIVE ONES MATRIX AUGMENTATION is NP-complete.** Source: Garey and Johnson (1979),
[SR16]; Booth (1975). -/
public theorem_wanted consecutiveOnesMatrixAugmentation_npComplete :
    consecutiveOnesMatrixAugmentationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L consecutiveOnesMatrixAugmentationDec

end MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentation

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCULAR ONES MATRIX AUGMENTATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR16] CONSECUTIVE ONES MATRIX
AUGMENTATION, pp. 229-230, comment: "Variant in which we ask instead that A' have the circular
ones property is also NP-complete" (no separate attribution; the entry cites [Booth, 1975] and
[Papadimitriou, 1976a] for the consecutive ones problem; K. S. Booth, *PQ-Tree Algorithms*,
Ph.D. thesis, University of California, Berkeley (1975); not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CircularOnesMatrixAugmentationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularOnesMatrixAugmentation

open MetaMathlibExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentation

/-!
# CIRCULAR ONES MATRIX AUGMENTATION is NP-complete

INSTANCE: an `m × n` matrix `A` of `0`'s and `1`'s and a positive integer `K`. QUESTION: is
there a matrix `A'`, obtained from `A` by changing `K` or fewer `0` entries to `1`'s, such that
`A'` has the circular ones property, i.e. the columns of `A'` can be permuted so that in each
row either all the `1`'s or all the `0`'s occur consecutively?

This is the variant of [SR16] CONSECUTIVE ONES MATRIX AUGMENTATION
(`WantedExt.Complexity.NPComplete.ConsecutiveOnesMatrixAugmentationWanted`) recorded in Garey
and Johnson's comment; the circular ones property is the one Garey and Johnson define in
[SR14]. The instance, its well-formedness, the entries `entry i r c` of `A` and the matrix `A'`
(a function `B : Fin m → Fin n → Bool` that is `1` wherever `A` is `1`, with at most `K`
changed entries) are those of the parent. A permutation of the columns is
`σ : Equiv.Perm (Fin n)`: column `j` of the permuted matrix is column `σ j` of `B`. The entries
equal to `b` of a row occur consecutively when every position between two positions holding
`b` also holds `b` (`CircularOnesSubmatrix.EntriesConsecutive` of
`WantedExt.Complexity.NPComplete.CircularOnesSubmatrixWanted`, applied to the row
`List.ofFn (B r)`); the question asks this for each row with `b = 1` or with `b = 0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CIRCULAR ONES MATRIX AUGMENTATION is NP-complete.** Source: Garey and Johnson (1979),
[SR16], comment. -/
public theorem_wanted circularOnesMatrixAugmentation_npComplete :
    circularOnesMatrixAugmentationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circularOnesMatrixAugmentationDec

end MetaMathlibExt.Complexity.NPComplete.CircularOnesMatrixAugmentation

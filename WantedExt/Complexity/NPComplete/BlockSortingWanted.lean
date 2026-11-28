/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BLOCK SORTING is NP-complete

Source:
W. W. Bein, L. L. Larmore, S. Latifi and I. H. Sudborough, "Block sorting is hard",
Proc. International Symposium on Parallel Architectures, Algorithms and Networks (I-SPAN 2002),
307-312, doi:10.1109/ISPAN.2002.1004305; journal version, International Journal of Foundations
of Computer Science 14 (2003), 425-437, doi:10.1142/S0129054103001820;
N. S. Narayanaswamy and S. Roy, "On approximability of block sorting", arXiv:1110.0892 (2011),
Section 2 (the definitions and the decision problem used here).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BlockSortingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BlockSorting

/-!
# BLOCK SORTING is NP-complete

Narayanaswamy and Roy (2011), Section 2: a permutation `π` of `[n] = {1, 2, …, n}` is written as
the string `π₁π₂…πₙ`, and `id` is the sorted (identity) permutation `1 2 … n`. "A block is a
maximal substring of a given permutation `π`, which is also a substring of the identity
permutation `id`." "A block move picks up a block and places it elsewhere in the permutation."
The block sorting distance `bs(π)` is the minimum number of block moves needed to sort `π`.
BLOCK SORTING: INPUT: a permutation `π` and an integer `m`. QUESTION: is `bs(π) ≤ m`?
Bein, Larmore, Latifi and Sudborough (2002, 2003) prove the problem NP-hard by a reduction from
3SAT. It is in NP: `n` block moves always suffice (moving the block that starts with `b` to just
after the block that ends with `b - 1` merges two blocks), so a certificate lists at most
`min(m, n)` intermediate permutations, each step checked in polynomial time.

The permutation is the list `[π₁, …, πₙ]`, a permutation of `[1, 2, …, n]` (`identity n`).
Substrings are contiguous sublists, Mathlib's `List.IsInfix` (`<:+:`). Blocks are taken in the
permutation the move is applied to. A block move writes `π = A ++ B ++ C` with `B` a block and
inserts `B` at another place of `A ++ C`; "elsewhere" is the condition that the result differs
from `π`. A sequence of block moves is a `List.IsChain` of permutations from `π` to the identity.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BLOCK SORTING is NP-complete.** Source: Bein, Larmore, Latifi and Sudborough (2002, 2003);
Narayanaswamy and Roy (2011), Section 2. -/
public theorem_wanted blockSorting_npComplete :
    blockSortingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L blockSortingDec

end MetaMathlibExt.Complexity.NPComplete.BlockSorting

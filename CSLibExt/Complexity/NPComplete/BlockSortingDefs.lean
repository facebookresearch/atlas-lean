/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Perm.Basic

/-!
# BLOCK SORTING: definitions

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

Source:
W. W. Bein, L. L. Larmore, S. Latifi and I. H. Sudborough, "Block sorting is hard",
Proc. International Symposium on Parallel Architectures, Algorithms and Networks (I-SPAN 2002),
307-312, doi:10.1109/ISPAN.2002.1004305; journal version, International Journal of Foundations
of Computer Science 14 (2003), 425-437, doi:10.1142/S0129054103001820;
N. S. Narayanaswamy and S. Roy, "On approximability of block sorting", arXiv:1110.0892 (2011),
Section 2 (the definitions and the decision problem used here).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BlockSorting

/-- An instance: the permutation `π` as the list `[π₁, …, πₙ]`, and the bound `m`. -/
abbrev BlockSortingInstance := List ℕ × ℕ

/-- The identity permutation `id = 1 2 … n`. -/
def identity (n : ℕ) : List ℕ := List.range' 1 n

/-- `B` is a block of `π`: a maximal substring of `π` that is also a substring of the identity
permutation of the same length (every substring of `π` that contains `B` and is a substring of
the identity is `B` itself). Blocks are nonempty. -/
def IsBlock (π B : List ℕ) : Prop :=
  B ≠ [] ∧ B <:+: π ∧ B <:+: identity π.length ∧
    ∀ B' : List ℕ, B <:+: B' → B' <:+: π → B' <:+: identity π.length → B' = B

/-- A block move from `π` to `π'`: pick up a block `B` of `π = A ++ B ++ C` and place it
elsewhere, `π' = X ++ B ++ Y` with `X ++ Y = A ++ C` and `π' ≠ π`. -/
def BlockMove (π π' : List ℕ) : Prop :=
  ∃ A B C X Y : List ℕ, π = A ++ B ++ C ∧ IsBlock π B ∧ X ++ Y = A ++ C ∧
    π' = X ++ B ++ Y ∧ π' ≠ π

/-- Well-formedness of an instance: `π` is a permutation of `[1, 2, …, n]`, for `n` its
length. -/
def WellFormed (i : BlockSortingInstance) : Prop :=
  i.1.Perm (identity i.1.length)

/-- `bs(π) ≤ m`: a sequence `π, π₁, …, π_k` with `k ≤ m`, each a block move from the previous
one, ends in the identity permutation. -/
def BlockSortingFeasible (i : BlockSortingInstance) : Prop :=
  ∃ s : List (List ℕ), s.length ≤ i.2 ∧ (i.1 :: s).IsChain BlockMove ∧
    (i.1 :: s).getLast (List.cons_ne_nil _ _) = identity i.1.length

open Classical in
/-- BLOCK SORTING as a decision problem over bitstrings. -/
noncomputable def blockSortingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BlockSortingInstance) x with
  | some i => decide (WellFormed i ∧ BlockSortingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BlockSorting

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BLOCK SORTING: definitions

Source:
W. W. Bein, L. L. Larmore, S. Latifi and I. H. Sudborough, "Block sorting is hard",
Proc. International Symposium on Parallel Architectures, Algorithms and Networks (I-SPAN 2002),
307-312, doi:10.1109/ISPAN.2002.1004305; journal version, International Journal of Foundations
of Computer Science 14 (2003), 425-437, doi:10.1142/S0129054103001820;
N. S. Narayanaswamy and S. Roy, "On approximability of block sorting", arXiv:1110.0892 (2011),
Section 2 (the definitions and the decision problem used here).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Perm.Basic

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

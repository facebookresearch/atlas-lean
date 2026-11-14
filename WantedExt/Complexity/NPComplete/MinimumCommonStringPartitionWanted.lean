/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM COMMON STRING PARTITION is NP-complete

Source:
A. Goldstein, P. Kolman and J. Zheng, "Minimum common string partition problem: hardness and
approximations", Electronic Journal of Combinatorics 12 (2005), #R50, doi:10.37236/1947,
Theorem 2.2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCommonStringPartition

/-!
# MINIMUM COMMON STRING PARTITION is NP-complete

A partition of a string `A` is a sequence `P = (P₁, P₂, …, P_m)` of strings, the blocks, whose
concatenation `P₁ P₂ ⋯ P_m` is `A`. For a partition `P` of `A` and a partition `Q` of `B`, the
pair `⟨P, Q⟩` is a common partition of `A` and `B` if `Q` is a permutation of `P`; its number
of blocks is `m`. Two strings are related if every letter occurs the same number of times in
both, the necessary and sufficient condition for a common partition to exist. INSTANCE: two
related strings `A` and `B` and a non-negative integer `K`. QUESTION: is there a common
partition of `A` and `B` with at most `K` blocks?

This is the decision version of MCSP (find a common partition with the minimum number of
blocks). Letters are natural numbers (the alphabet is unbounded), strings are lists of letters,
and a partition is the list of its blocks. Related strings are lists that are permutations of
each other.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the strings `A` and `B`, and the bound `K` on the number of blocks. -/
abbrev MinimumCommonStringPartitionInstance := List ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: `A` and `B` are related (permutations of each other). -/
def WellFormed (i : MinimumCommonStringPartitionInstance) : Prop :=
  i.1.Perm i.2.1

/-- Some common partition `⟨P, Q⟩` of `A` and `B` has at most `K` blocks: `P` concatenates
to `A`, `Q` concatenates to `B`, and `Q` is a permutation of `P`. -/
def MinimumCommonStringPartitionFeasible (i : MinimumCommonStringPartitionInstance) : Prop :=
  ∃ P Q : List (List ℕ), P.flatten = i.1 ∧ Q.flatten = i.2.1 ∧ Q.Perm P ∧ P.length ≤ i.2.2

open Classical in
/-- MINIMUM COMMON STRING PARTITION as a decision problem over bitstrings. -/
noncomputable def minimumCommonStringPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCommonStringPartitionInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCommonStringPartitionFeasible i)
  | none => false

/-- **MINIMUM COMMON STRING PARTITION is NP-complete.** Source: Goldstein, Kolman and Zheng
(2005), Theorem 2.2. -/
public theorem_wanted minimumCommonStringPartition_npComplete :
    minimumCommonStringPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCommonStringPartitionDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCommonStringPartition

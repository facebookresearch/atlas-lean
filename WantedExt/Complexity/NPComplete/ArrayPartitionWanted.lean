/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ARRAY PARTITION is NP-complete

Source:
M. Grigni and F. Manne, "On the complexity of the generalized block distribution", in *Parallel
Algorithms for Irregularly Structured Problems (IRREGULAR '96)*, Lecture Notes in Computer
Science 1117, Springer (1996), 319-326, doi:10.1007/BFb0030123, Theorem 2 ("GBD is
NP-Complete"; the reduction from BALANCED COMPLETE BIPARTITE SUBGRAPH builds a square zero-one
array with `p = q` and `K = 1`, and the conclusion notes that GBD "remains NP-complete for any
derived cost function such as the sum of the elements in a block");
P. Crescenzi and V. Kann, *A compendium of NP optimization problems* (2000), problem
MINIMUM ARRAY PARTITION.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ArrayPartition

/-!
# ARRAY PARTITION is NP-complete

INSTANCE: an `n × n` array `A` of non-negative integers, a positive integer `p`, and a
non-negative integer `K`.
QUESTION: are there `p - 1` horizontal dividers `0 = h_0 < h_1 < ⋯ < h_p = n` and `p - 1`
vertical dividers `0 = v_0 < v_1 < ⋯ < v_p = n`, partitioning `A` into `p²` blocks, such that
the sum of the entries of every block is at most `K`?

This is the decision version of the compendium's MINIMUM ARRAY PARTITION, the generalized block
distribution of Grigni and Manne with `p = q` and the sum of the entries as the cost of a block.
Block `(i, j)` consists of the rows `r` with `h_i ≤ r < h_{i+1}` and the columns `c` with
`v_j ≤ c < v_{j+1}` (rows and columns indexed from `0`, so the compendium's `h_{j-1} < y ≤ h_j`
becomes `h_j ≤ r < h_{j+1}`). Grigni and Manne allow empty intervals (`h_i ≤ h_{i+1}`); with
non-negative entries splitting a block never increases a block sum, so when `p ≤ n` any
distribution with empty intervals can be refined to one with `p` nonempty intervals of no larger
cost, and the strict dividers of the compendium give the same problem on the instances of their
reduction, which have `p ≤ n` (for `p > n` there are no strict dividers, a no-instance). Their
reduction uses a zero-one array, so the problem is NP-complete in the strong
sense; the entries are written in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the rows of the array `A`, the number `p`, and the bound `K`. -/
abbrev ArrayPartitionInstance := List (List ℕ) × ℕ × ℕ

/-- The entry `A[r, c]` (`0`-based), read as `0` outside the array. -/
def entry (A : List (List ℕ)) (r c : ℕ) : ℕ := (A.getD r []).getD c 0

/-- `h` lists dividers `0 = h_0 < h_1 < ⋯ < h_p = n`. -/
def IsDividers (n p : ℕ) (h : List ℕ) : Prop :=
  h.length = p + 1 ∧ h.getD 0 0 = 0 ∧ h.getD p 0 = n ∧ ∀ k < p, h.getD k 0 < h.getD (k + 1) 0

/-- The sum of the entries of block `(i, j)`: rows `h_i ≤ r < h_{i+1}`, columns
`v_j ≤ c < v_{j+1}`. -/
def blockSum (A : List (List ℕ)) (h v : List ℕ) (i j : ℕ) : ℕ :=
  ∑ r ∈ Finset.Ico (h.getD i 0) (h.getD (i + 1) 0),
    ∑ c ∈ Finset.Ico (v.getD j 0) (v.getD (j + 1) 0), entry A r c

/-- Well-formedness of an instance: the array is square (every row has `n` entries, where `n`
is the number of rows), and `p` is positive (`K` is any natural number, as in Grigni and Manne's
"an integer `K`"; block sums are non-negative). -/
def WellFormed (i : ArrayPartitionInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧ 0 < i.2.1

/-- Some horizontal and vertical dividers make every one of the `p²` block sums at most `K`. -/
def ArrayPartitionFeasible (i : ArrayPartitionInstance) : Prop :=
  ∃ h v : List ℕ, IsDividers i.1.length i.2.1 h ∧ IsDividers i.1.length i.2.1 v ∧
    ∀ a < i.2.1, ∀ b < i.2.1, blockSum i.1 h v a b ≤ i.2.2

open Classical in
/-- ARRAY PARTITION as a decision problem over bitstrings. -/
noncomputable def arrayPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ArrayPartitionInstance) x with
  | some i => decide (WellFormed i ∧ ArrayPartitionFeasible i)
  | none => false

/-- **ARRAY PARTITION is NP-complete.** Source: Grigni and Manne (1996), Theorem 2; Crescenzi and
Kann, MINIMUM ARRAY PARTITION. -/
public theorem_wanted arrayPartition_npComplete :
    arrayPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L arrayPartitionDec

end MetaMathlibExt.Complexity.NPComplete.ArrayPartition

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOUBLE DIGEST: definitions

Source:
L. Goldstein and M. S. Waterman, "Mapping DNA by stochastic relaxation", Advances in Applied
Mathematics 8 (1987), 194-207, doi:10.1016/0196-8858(87)90013-3;
M.-Y. Kao, J. Samet and W.-K. Sung, "The enhanced double digest problem for DNA physical
mapping", arXiv:cs/0102010 (2001), Section 1 (records the problem and Goldstein and Waterman's
NP-hardness proof by a reduction from set partition);
M. Cieliebak, S. Eidenbenz and G. J. Woeginger, "Double digest revisited: complexity and
approximability in the presence of noisy data", COCOON 2003, Lecture Notes in Computer Science
2697 (2003), 519-527, doi:10.1007/3-540-45071-8_52.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Sort

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DoubleDigest

/-- An instance: the fragment lengths `A` (enzyme 1), `B` (enzyme 2) and `C` (both enzymes),
as lists read as multisets. -/
abbrev DoubleDigestInstance := List ℕ × List ℕ × List ℕ

/-- Well-formedness of an instance: `A` and `B` are nonempty (each enzyme yields at least one
fragment), all lengths are positive, and `∑ A = ∑ B = ∑ C`. -/
def WellFormed (i : DoubleDigestInstance) : Prop :=
  i.1 ≠ [] ∧ i.2.1 ≠ [] ∧ (∀ x ∈ i.1, 0 < x) ∧ (∀ x ∈ i.2.1, 0 < x) ∧ (∀ x ∈ i.2.2, 0 < x) ∧
    i.1.sum = i.2.1.sum ∧ i.2.1.sum = i.2.2.sum

/-- The cut points of an ordering `a` of fragment lengths: its prefix sums
`0, a₁, a₁ + a₂, ..., ∑ a`. -/
def cutPoints (a : List ℕ) : List ℕ :=
  a.scanl (· + ·) 0

/-- The fragment lengths cut out by a sorted list of cut points: the differences of
consecutive entries. -/
def fragments (l : List ℕ) : List ℕ :=
  List.zipWith (· - ·) l.tail l

/-- Some orderings `a` of `A` and `b` of `B` have disjoint internal cut points, and their merged
cut points (in increasing order) have fragment lengths forming the multiset `C`. -/
def DoubleDigestFeasible (i : DoubleDigestInstance) : Prop :=
  ∃ a b : List ℕ, a.Perm i.1 ∧ b.Perm i.2.1 ∧
    (cutPoints a).tail.dropLast.Disjoint (cutPoints b).tail.dropLast ∧
    (fragments (((cutPoints a ++ cutPoints b).dedup).insertionSort (· ≤ ·))).Perm i.2.2

open Classical in
/-- DOUBLE DIGEST as a decision problem over bitstrings. -/
noncomputable def doubleDigestDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DoubleDigestInstance) x with
  | some i => decide (WellFormed i ∧ DoubleDigestFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DoubleDigest

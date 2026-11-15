/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOUBLE DIGEST is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Sort

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DoubleDigest

/-!
# DOUBLE DIGEST is NP-complete

INSTANCE: multisets `A`, `B` and `C` of positive integers with `∑ A = ∑ B = ∑ C` (the lengths
of the fragments of a DNA sequence cut by enzyme 1, by enzyme 2, and by both enzymes).
QUESTION: are there orderings of `A` and of `B` such that, when both are laid out from the same
starting point, the union of their cut points cuts the sequence into fragments whose lengths
form the multiset `C`? As in the source formulation, the restriction sites of the two enzymes
do not coincide: apart from the common ends of the sequence, no cut point of `A` is a cut point
of `B` (so `|C| = |A| + |B| - 1` for every solution).

Kao, Samet and Sung define the problem this way ("It is a biology fact that the restriction
sites for enzymes A and B do not coincide"; `A`, `B`, `C` the multisets of fragment lengths
from enzyme A, enzyme B and both) and record that Goldstein and Waterman "showed that the DD
problem is NP-hard by reducing the set partition problem to it". Cieliebak, Eidenbenz and
Woeginger revisit the problem and its complexity. The orderings are a polynomial certificate,
so the problem is in NP. Lengths are natural numbers in binary encoding.

The multisets are lists, compared up to permutation (`List.Perm`). An ordering of `A` is a list
`a` with `a.Perm A`; its cut points are its prefix sums `0, a₁, a₁ + a₂, ..., ∑ a`
(`List.scanl`); its internal cut points drop the first (`0`) and the last (`∑ a`). The internal
cut points of the two orderings are disjoint, and all cut points are merged into one
duplicate-free list (`List.dedup`, which merges the common ends) and sorted
(`List.insertionSort`); the fragments are the differences of consecutive cut points.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **DOUBLE DIGEST is NP-complete.** Source: Goldstein and Waterman (1987); Kao, Samet and Sung
(2001); Cieliebak, Eidenbenz and Woeginger (2003). -/
public theorem_wanted doubleDigest_npComplete :
    doubleDigestDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L doubleDigestDec

end MetaMathlibExt.Complexity.NPComplete.DoubleDigest

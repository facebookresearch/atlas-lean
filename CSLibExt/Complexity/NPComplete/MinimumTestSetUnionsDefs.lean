/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumTestSetDefs

/-!
# MINIMUM TEST SET with unions of tests: definitions

INSTANCE: a collection `C` of subsets of a finite set `S`, and a positive integer `K ≤ |C|`.
QUESTION: is there a collection `C'` with `|C'| ≤ K`, each member of which is a member of `C` or
a union of members of `C` (the comment's variant: `C'` can contain unions of subsets in `C` as
well as subsets in `C`), such that for each pair of distinct elements `u, v ∈ S` there is some
set `c ∈ C'` that contains exactly one of `u` and `v`?

The instance is that of `MinimumTestSetWanted`: `S = {0, …, n - 1}`, and `C` is a list of
duplicate-free lists of elements of `S`. A test of `C'` is given by the sublist `t` of `C` whose
union it is (a single member of `C` is the union of a one-element sublist); an element lies in
that test when it lies in some member of `t`. `WellFormed` adds that the members of `C` are
distinct as sets (so the list length is `|C|`) and Garey and Johnson's bound `0 < K ≤ |C|`,
neither of which the parent module imposes.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP6] MINIMUM TEST SET, p. 222,
comment: the variant in which `C'` can contain unions of subsets in `C` as well as subsets in
`C` is also NP-complete (reference: T. Ibaraki, T. Kameda, and S. Toida, "NP-complete diagnosis
problems on system graphs", unpublished manuscript (1977)).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSetUnions

open MetaMathlibExt.Complexity.NPComplete.MinimumTestSet

/-- Well-formedness of an instance: the parent's well-formedness (every test is a
duplicate-free list of elements of `S`), the tests are distinct as sets, and `0 < K ≤ |C|`. -/
def WellFormed (i : MinimumTestSetInstance) : Prop :=
  MinimumTestSet.WellFormed i ∧ (i.2.1.map List.toFinset).Nodup ∧ 0 < i.2.2 ∧
    i.2.2 ≤ i.2.1.length

/-- Some collection of at most `K` tests, each the union of a sublist of `C`, distinguishes every
pair of distinct elements of `S`: some test contains exactly one of them. -/
def MinimumTestSetUnionsFeasible (i : MinimumTestSetInstance) : Prop :=
  ∃ T : List (List (List ℕ)), (∀ t ∈ T, t.Sublist i.2.1) ∧ T.length ≤ i.2.2 ∧
    ∀ a < i.1, ∀ b < i.1, a ≠ b →
      ∃ t ∈ T, ((∃ s ∈ t, a ∈ s) ∧ ¬ ∃ s ∈ t, b ∈ s) ∨ (¬ (∃ s ∈ t, a ∈ s) ∧ ∃ s ∈ t, b ∈ s)

open Classical in
/-- MINIMUM TEST SET with unions of tests as a decision problem over bitstrings. -/
noncomputable def minimumTestSetUnionsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumTestSetInstance) x with
  | some i => decide (WellFormed i ∧ MinimumTestSetUnionsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSetUnions

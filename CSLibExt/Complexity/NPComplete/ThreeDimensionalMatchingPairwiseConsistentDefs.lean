/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeDimensionalMatchingDefs

/-!
# 3-DIMENSIONAL MATCHING for pairwise consistent triples: definitions

INSTANCE: a set `M ⊆ W × X × Y`, where `W`, `X`, and `Y` are disjoint sets having the same
number `q` of elements, such that `M` is pairwise consistent: for all elements `a`, `b`, `c`,
whenever there exist elements `w`, `x`, and `y` such that `(a, b, w) ∈ M`, `(a, x, c) ∈ M`, and
`(y, b, c) ∈ M`, then `(a, b, c) ∈ M`. QUESTION: does `M` contain a matching, i.e., a subset
`M' ⊆ M` such that `|M'| = q` and no two elements of `M'` agree in any coordinate?

This is 3-DIMENSIONAL MATCHING (`WantedExt.Complexity.NPComplete.ThreeDimensionalMatchingWanted`,
Garey and Johnson [SP1]) restricted as in the [SP1] comment: "Remains NP-complete if `M` is
'pairwise consistent,' ... (this follows from the proof of Theorem 3.1.2)", that is, from the
transformation from 3SAT in Section 3.1.2, whose triples are pairwise consistent. Garey and
Johnson give no other reference; their entry is the literature record. (Their comment prints
"elements `w`, `z`, and `y`"; the `z` is a misprint for the `x` of `(a, x, c)`.)

The instance (`q` and the list of triples, the three coordinates ranging over `0, …, q - 1`),
`ThreeDimensionalMatching.WellFormed` and
`ThreeDimensionalMatching.ThreeDimensionalMatchingFeasible` are reused unchanged; pairwise
consistency is added to well-formedness, with the three witnesses as list entries
`t₁ = (a, b, w)`, `t₂ = (a, x, c)` and `t₃ = (y, b, c)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP1] 3-DIMENSIONAL MATCHING, comment,
and the transformation from 3SAT in Section 3.1.2.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingPairwiseConsistent



open ThreeDimensionalMatching (ThreeDimensionalMatchingInstance)

/-- Pairwise consistency of the triples: whenever `(a, b, w)`, `(a, x, c)` and `(y, b, c)` are
triples, so is `(a, b, c)`. -/
def PairwiseConsistent (M : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ t₁ ∈ M, ∀ t₂ ∈ M, ∀ t₃ ∈ M, t₁.1 = t₂.1 → t₁.2.1 = t₃.2.1 → t₂.2.2 = t₃.2.2 →
    (t₁.1, t₁.2.1, t₂.2.2) ∈ M

/-- Well-formedness of an instance: a well-formed 3-DIMENSIONAL MATCHING instance whose triples
are pairwise consistent. -/
def WellFormed (i : ThreeDimensionalMatchingInstance) : Prop :=
  ThreeDimensionalMatching.WellFormed i ∧ PairwiseConsistent i.2

open Classical in
/-- 3-DIMENSIONAL MATCHING for pairwise consistent triples as a decision problem over
bitstrings. -/
noncomputable def threeDimensionalMatchingPairwiseConsistentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDimensionalMatchingInstance) x with
  | some i => decide (WellFormed i ∧ ThreeDimensionalMatching.ThreeDimensionalMatchingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingPairwiseConsistent
